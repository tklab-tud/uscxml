#include "OSGConverter.h"
#include <glog/logging.h>
#include "uscxml/config.h"

#include <osg/MatrixTransform>
#include <osgDB/ReadFile>
#include <osgDB/WriteFile>
#include <osgDB/Registry>
#include <osgGA/TrackballManipulator>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new OSGConverterProvider() );
	return true;
}
#endif

OSGConverter::OSGConverter() : _isRunning(false) {
}

OSGConverter::~OSGConverter() {
	_isRunning = false;
	std::set<tthread::thread*>::iterator threadIter = _threads.begin();
	while(threadIter != _threads.end()) {
		(*threadIter)->join();
	}
};

boost::shared_ptr<IOProcessorImpl> OSGConverter::create(Interpreter* interpreter) {
	boost::shared_ptr<OSGConverter> invoker = boost::shared_ptr<OSGConverter>(new OSGConverter());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data OSGConverter::getDataModelVariables() {
	Data data;
	return data;
}

void OSGConverter::send(const SendRequest& req) {

	/**
	 * we have to resolve all datamodel dependent strings first as
	 * we cannot access the datamodel from within another thread without locking
	 */

	// make a copy
	SendRequest actualReq(req);

	if (actualReq.params.find("source") == actualReq.params.end()) {
		// no explicit source
		if (actualReq.params.find("sourceexpr") != actualReq.params.end() && _interpreter->getDataModel()) {
			actualReq.params.insert(std::make_pair("source", _interpreter->getDataModel().evalAsString(actualReq.params.find("sourceexpr")->second)));
		} else {
			LOG(ERROR) << "SendRequests for osginvoker missing source or sourceExpr and datamodel";
			return;
		}
	}

	if (actualReq.params.find("dest") == actualReq.params.end()) {
		// no explicit destination
		if (actualReq.params.find("destexpr") != actualReq.params.end() && _interpreter->getDataModel()) {
			actualReq.params.insert(std::make_pair("dest", _interpreter->getDataModel().evalAsString(actualReq.params.find("destexpr")->second)));
		} else {
			LOG(ERROR) << "SendRequests for osginvoker missing dest or destExpr and datamodel";
			return;
		}
	}

	if (actualReq.params.find("format") == actualReq.params.end()) {
		// no explicit format
		if (actualReq.params.find("formatexpr") != actualReq.params.end() && _interpreter->getDataModel()) {
			actualReq.params.insert(std::make_pair("format", _interpreter->getDataModel().evalAsString(actualReq.params.find("formatexpr")->second)));
		} else {
			std::string format;
			size_t lastDot;
			std::string dest = req.params.find("dest")->second;
			if ((lastDot = dest.find_last_of(".")) != std::string::npos) {
				lastDot++;
				format = dest.substr(lastDot, dest.length() - lastDot);
			}
			if (format.length() == 0 || format.find_last_of(PATH_SEPERATOR) != std::string::npos) {
				// empty format or pathseperator in format
				format = "png";
			}
			actualReq.params.insert(std::make_pair("format", format));
		}
	}

	if (actualReq.params.find("height") == actualReq.params.end()) {
		// no explicit height
		if (actualReq.params.find("heightexpr") != actualReq.params.end() && _interpreter->getDataModel()) {
			actualReq.params.insert(std::make_pair("height", _interpreter->getDataModel().evalAsString(actualReq.params.find("heightexpr")->second)));
		}
	}

	if (actualReq.params.find("width") == actualReq.params.end()) {
		// no explicit width
		if (actualReq.params.find("widthexpr") != actualReq.params.end() && _interpreter->getDataModel()) {
			actualReq.params.insert(std::make_pair("width", _interpreter->getDataModel().evalAsString(actualReq.params.find("widthexpr")->second)));
		}
	}

	_workQueue.push(actualReq);
}

void OSGConverter::cancel(const std::string sendId) {
}

void OSGConverter::invoke(const InvokeRequest& req) {
	int nrThreads = 1;
	if (req.params.find("threads") != req.params.end() && isNumeric(req.params.find("threads")->second.c_str(), 10)) {
		nrThreads = strTo<int>(req.params.find("threads")->second);
	}

	_isRunning = true;
	for (int i = 0; i < nrThreads; i++) {
		_threads.insert(new tthread::thread(OSGConverter::run, this));
	}
}

void OSGConverter::run(void* instance) {
	OSGConverter* INSTANCE = (OSGConverter*)instance;
	while(true) {
		SendRequest req = INSTANCE->_workQueue.pop();
		if (INSTANCE->_isRunning) {
			INSTANCE->process(req);
		} else {
			return;
		}
	}
}

void OSGConverter::process(const SendRequest& req) {

	int width = (req.params.find("width") != req.params.end() ? strTo<int>(req.params.find("width")->second) : 640);
	int height = (req.params.find("height") != req.params.end() ? strTo<int>(req.params.find("height")->second) : 480);

	assert(req.params.find("source") != req.params.end());
	assert(req.params.find("dest") != req.params.end());
	assert(req.params.find("format") != req.params.end());

	std::string source = req.params.find("source")->second;
	std::string dest = req.params.find("dest")->second;
	std::string format = req.params.find("format")->second;

	osg::ref_ptr<osg::Node> sceneGraph = setupGraph(source);

	osgDB::ReaderWriter::WriteResult result;
	if (osgDB::Registry::instance()->getReaderWriterForExtension(format) != NULL) {
		// write as another 3D file
		result = osgDB::Registry::instance()->writeNode(*sceneGraph, dest, osgDB::Registry::instance()->getOptions());
	}

	if (result.error()) {
		// make a screenshot
		osgViewer::ScreenCaptureHandler::CaptureOperation* cOp = new NameRespectingWriteToFile(dest,
		        format,
		        osgViewer::ScreenCaptureHandler::WriteToFile::OVERWRITE
		                                                                                      );

		osgViewer::ScreenCaptureHandler* captureHandler = new osgViewer::ScreenCaptureHandler(cOp, -1);

		osgViewer::Viewer viewer;
		viewer.setSceneData(sceneGraph);
		viewer.setCameraManipulator(new osgGA::TrackballManipulator());
		viewer.addEventHandler(captureHandler);
		captureHandler->startCapture();

		osg::DisplaySettings* ds = osg::DisplaySettings::instance().get();
		osg::ref_ptr<osg::GraphicsContext::Traits> traits = new osg::GraphicsContext::Traits(ds);
		traits->width = width;
		traits->height = height;
		traits->pbuffer = true;
		osg::ref_ptr<osg::GraphicsContext> gc = osg::GraphicsContext::createGraphicsContext(traits.get());
		GLenum pbuffer = gc->getTraits()->doubleBuffer ? GL_BACK : GL_FRONT;

		viewer.getCamera()->setGraphicsContext(gc.get());
		viewer.getCamera()->setViewport(new osg::Viewport(0,0,traits->width,traits->height));
		viewer.getCamera()->setDrawBuffer(pbuffer);
		viewer.getCamera()->setReadBuffer(pbuffer);

		// set background color
		viewer.getCamera()->setClearColor(osg::Vec4f(1.0f,1.0f,1.0f,1.0f));
		viewer.getCamera()->setClearMask(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);

		((osg::MatrixTransform*)sceneGraph.get())->setMatrix(requestToModelPose(req));
		viewer.getCamera()->setViewMatrix(requestToCamPose(req));

//    viewer.home();

		// perform one viewer iteration
		viewer.realize();
		viewer.frame();
	}
}

osg::Matrix OSGConverter::requestToModelPose(const SendRequest& req) {
	double pitch = (req.params.find("pitch") != req.params.end() ? strTo<int>(req.params.find("pitch")->second) : 0);
	double roll = (req.params.find("roll") != req.params.end() ? strTo<int>(req.params.find("roll")->second) : 0);
	double yaw = (req.params.find("yaw") != req.params.end() ? strTo<int>(req.params.find("yaw")->second) : 0);

	return eulerToMatrix(pitch, roll, yaw);
//  osg::Matrix m;
//  m.makeIdentity();
//  return m;
}

osg::Matrix OSGConverter::requestToCamPose(const SendRequest& req) {
	return eulerToMatrix(0, 0, 0);
}

osg::ref_ptr<osg::Node> OSGConverter::setupGraph(const std::string filename) {

	/**
	 *  root (model pose)
	 *    - modelCenter (center model)
	 *      - model (actual model)
	 */

	long now = tthread::chrono::system_clock::now();

	{
		// get some privacy
		tthread::lock_guard<tthread::recursive_mutex> lock(_cacheMutex);

		// do we have it in the cache?
		if (_models.find(filename) == _models.end()) {
			osg::ref_ptr<osg::Node> model = osgDB::readNodeFile(filename);
			if (!model.valid()) {
				LOG(ERROR) << "Cannot load model from " << filename;
				return new osg::MatrixTransform();
			}
			_models[filename] = std::make_pair(now, model);
		}

		// remove old models from cache
		std::map<std::string, std::pair<long, osg::ref_ptr<osg::Node> > >::iterator modelIter = _models.begin();
		while(modelIter != _models.end()) {
			// delete every model unused for 1 minutes
			if (now - modelIter->second.first > 60000) {
				_models.erase(modelIter++);
			} else {
				modelIter++;
			}
		}
	}

	osg::ref_ptr<osg::MatrixTransform> root = new osg::MatrixTransform();

	osg::ref_ptr<osg::Node> model = _models[filename].second;
	_models[filename].first = now;

	// translation matrix to move model into center
	osg::ref_ptr<osg::MatrixTransform> modelCenter = new osg::MatrixTransform();
	modelCenter->addChild(model);

	// move bounding sphere center into origin
	osg::BoundingSphere bs = model->getBound();
	modelCenter->setMatrix(osg::Matrix::translate(bs.center() *= -1));

	// add to model pose matrix
	root->addChild(modelCenter);

	return root;
}

osg::Matrix OSGConverter::eulerToMatrix(double pitch, double roll, double yaw) {
	// see http://www.flipcode.com/documents/matrfaq.html#Q36
	osg::Matrix m;
	m.makeIdentity();

	double A = cos(pitch);
	double B = sin(pitch);
	double C = cos(roll);
	double D = sin(roll);
	double E = cos(yaw);
	double F = sin(yaw);

	double AD = A * D;
	double BD = B * D;

	m(0,0) = C * E;
	m(0,1) = -C * F;
	m(0,2) = -D;
	m(1,0) = -BD * E + A * F;
	m(1,1) = BD * F + A * E;
	m(1,2) = -B * C;
	m(2,0) = AD * E + B * F;
	m(2,1) = -AD * F + B * E;
	m(2,2) = A * C;

	m(0,3) = m(1,3) = m(2,3) = m(3,0) = m(3,1) = m(3,2) = 0;
	m(3,3) = 1;

	return m;
}

void OSGConverter::matrixToEuler(const osg::Matrix& m, double& pitch, double& roll, double& yaw) {
	// see: http://www.flipcode.com/documents/matrfaq.html#Q37
	double angle_x, angle_z;
	double D = -1 * asin(m(0,2));        /* Calculate Y-axis angle */
	double angle_y = D;
	double C =  cos(angle_y);

	/* Gimball lock? */
	if ( fabs( C ) > 0.005 ) {
		double tr_x =  m(2,2) / C;           /* No, so get X-axis angle */
		double tr_y = -1 * m(1,2)  / C;
		angle_x  = atan2( tr_y, tr_x );
		tr_x =  m(0,0) / C;                  /* Get Z-axis angle */
		tr_y = -1 * m(0,1) / C;
		angle_z  = atan2( tr_y, tr_x );
	} else {
		/* Gimball lock has occurred */
		angle_x = 0;                      /* Set X-axis angle to zero */
		double tr_x = m(1,1);                 /* And calculate Z-axis angle */
		double tr_y = m(1,0);
		angle_z = atan2( tr_y, tr_x );
	}

	pitch = fmod(angle_x, 2 * M_PI );  /* Clamp all angles to range */
	roll = fmod( angle_y, 2 * M_PI );
	yaw = fmod( angle_z, 2 * M_PI );
}

void OSGConverter::NameRespectingWriteToFile::operator()(const osg::Image& image, const unsigned int context_id) {
	osgDB::writeImageFile(image, _filename);
}

}