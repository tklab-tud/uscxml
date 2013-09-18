#include "OSGConverter.h"
#include <glog/logging.h>
#include "uscxml/config.h"

#include <osg/MatrixTransform>
#include <osg/Node>
#include <osg/Group>
#include <osg/ComputeBoundsVisitor>
#include <osgDB/ReadFile>
#include <osgDB/WriteFile>
#include <osgDB/Registry>
#include <osgGA/TrackballManipulator>
#include <osgGA/AnimationPathManipulator>
#include <osg/ShapeDrawable>

#include <boost/lexical_cast.hpp>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#define EVAL_PARAM_EXPR(param, expr, key) \
if (param.find(key) == param.end() && param.find(expr) != param.end() && _interpreter->getDataModel()) \
  param.insert(std::make_pair(key, _interpreter->getDataModel().evalAsString(param.find(expr)->second.atom)));

#define CAST_PARAM(param, var, key, type) \
if (param.find(key) != param.end()) { \
  try { var = boost::lexical_cast<type>(param.find(key)->second.atom); } \
  catch(...) { LOG(ERROR) << "Attribute " key " of sendrequest to osgconverter is of invalid format: " << param.find(key)->second.atom; } \
}


namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new OSGConverterProvider() );
	return true;
}
#endif

OSGConverter::OSGConverter() : _isRunning(false) {
//  osg::setNotifyLevel(osg::DEBUG_FP);
	osg::setNotifyLevel(osg::FATAL);
}

OSGConverter::~OSGConverter() {
	_isRunning = false;
	std::set<tthread::thread*>::iterator threadIter = _threads.begin();
	while(threadIter != _threads.end()) {
		(*threadIter)->join();
	}
};

boost::shared_ptr<InvokerImpl> OSGConverter::create(InterpreterImpl* interpreter) {
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
			actualReq.params.insert(std::make_pair("source", _interpreter->getDataModel().getStringAsData(actualReq.params.find("sourceexpr")->second)));
		} else {
			LOG(ERROR) << "SendRequests for osginvoker missing source or sourceExpr and datamodel";
			return;
		}
	}

	if (actualReq.params.find("dest") == actualReq.params.end()) {
		// no explicit destination
		if (actualReq.params.find("destexpr") != actualReq.params.end() && _interpreter->getDataModel()) {
			actualReq.params.insert(std::make_pair("dest", _interpreter->getDataModel().getStringAsData(actualReq.params.find("destexpr")->second)));
			boost::algorithm::replace_all(actualReq.params.find("dest")->second.atom, "//", "/");
			boost::algorithm::replace_all(actualReq.params.find("dest")->second.atom, "\\\\", "\\");
		}
	}

	if (actualReq.params.find("autorotate") == actualReq.params.end()) {
		if (actualReq.params.find("autorotateexpr") != actualReq.params.end()) {
			if (_interpreter->getDataModel()) {
				actualReq.params.insert(std::make_pair("autorotate", _interpreter->getDataModel().getStringAsData(actualReq.params.find("autorotateexpr")->second)));
			} else {
				LOG(ERROR) << "SendRequests for osginvoker ncludes autorotateexpr but no datamodel is specified";
				return;
			}
		}
	}

	if (actualReq.params.find("format") == actualReq.params.end()) {
		// no explicit format
		if (actualReq.params.find("formatexpr") != actualReq.params.end() && _interpreter->getDataModel()) {
			actualReq.params.insert(std::make_pair("format", _interpreter->getDataModel().getStringAsData(actualReq.params.find("formatexpr")->second)));
		} else {
			std::string format;
			std::string dest;
			if (Event::getParam(actualReq.params, "dest", dest)) {
				size_t lastDot;
				if ((lastDot = dest.find_last_of(".")) != std::string::npos) {
					lastDot++;
					format = dest.substr(lastDot, dest.length() - lastDot);
				}
			}
			if (format.length() == 0 || format.find_last_of(PATH_SEPERATOR) != std::string::npos) {
				// empty format or pathseperator in format
				format = "png";
			}
			actualReq.params.insert(std::make_pair("format", Data(format, Data::VERBATIM)));
		}
	}

	EVAL_PARAM_EXPR(actualReq.params, "heightexpr", "height");
	EVAL_PARAM_EXPR(actualReq.params, "widthexpr", "width");
	EVAL_PARAM_EXPR(actualReq.params, "pitchexpr", "pitch");
	EVAL_PARAM_EXPR(actualReq.params, "rollexpr", "roll");
	EVAL_PARAM_EXPR(actualReq.params, "yawexpr", "yaw");
	EVAL_PARAM_EXPR(actualReq.params, "zoomexpr", "zoom");
	EVAL_PARAM_EXPR(actualReq.params, "xexpr", "x");
	EVAL_PARAM_EXPR(actualReq.params, "yexpr", "y");
	EVAL_PARAM_EXPR(actualReq.params, "zexpr", "z");

//  process(actualReq);
	_workQueue.push(actualReq);
}

void OSGConverter::cancel(const std::string sendId) {
}

void OSGConverter::invoke(const InvokeRequest& req) {
	int nrThreads = 1;
	
	if (req.params.find("threads") != req.params.end() && isNumeric(req.params.find("threads")->second.atom.c_str(), 10)) {
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

//  std::cout << req;

	int width = 640;
	int height = 480;
	Event::getParam(req.params, "width", width);
	Event::getParam(req.params, "height", height);

	assert(req.params.find("source") != req.params.end());
	assert(req.params.find("format") != req.params.end());

	std::string source;
	if (!Event::getParam(req.params, "source", source))
		reportFailure(req);

	std::string dest;
	Event::getParam(req.params, "dest", dest);

	std::string format;
	if (!Event::getParam(req.params, "format", format))
		reportFailure(req);

	bool autoRotate = true;
	if (req.params.find("autorotate") != req.params.end()) {
		if (boost::iequals(req.params.find("autorotate")->second.atom, "off") ||
				boost::iequals(req.params.find("autorotate")->second.atom, "0") ||
				boost::iequals(req.params.find("autorotate")->second.atom, "false")) {
			autoRotate = false;
		}
	}

	osg::ref_ptr<osg::Node> model = setupGraph(source, autoRotate);
	if (model->asGroup()->getNumChildren() == 0) {
		reportFailure(req);
		return;
	}

	osg::ref_ptr<osg::Group> sceneGraph = new osg::Group();
	sceneGraph->addChild(model);

	osgDB::ReaderWriter::WriteResult result;
	
	osg::ref_ptr<osgDB::ReaderWriter> writer = osgDB::Registry::instance()->getReaderWriterForExtension(format);
	if(writer.valid()) {
		std::stringstream ss;
		result = writer->writeNode(*sceneGraph, ss);
		if (result.success()) {
			if (dest.length() > 0) {
				std::ofstream outFile(dest.c_str());
				outFile << ss.str();
			}
			Data content(ss.str().c_str(), ss.str().size(), false);
			reportSuccess(req, content);
			return;
		}
	}
	
	/**
	 * If we failed to interpret the extension as another 3D file, try to make a screenshot.
	 */

	((osg::MatrixTransform*)model.get())->setMatrix(requestToModelPose(req));
	osg::BoundingSphere bs = model->getBound();

//  osg::ref_ptr<osg::MatrixTransform> scale = new osg::MatrixTransform();
//  scale->setMatrix(osg::Matrix::scale(bs.radius() / 5, bs.radius() / 5, bs.radius() / 5));
//  scale->addChild(getOrigin());
//  sceneGraph->addChild(scale);

	osgViewer::ScreenCaptureHandler::CaptureOperation* cOp = new NameRespectingWriteToFile(
	    dest,
	    format,
	    osgViewer::ScreenCaptureHandler::WriteToFile::OVERWRITE,
	    req, this);

	osgViewer::ScreenCaptureHandler* captureHandler = new osgViewer::ScreenCaptureHandler(cOp, -1);

	{
//		tthread::lock_guard<tthread::recursive_mutex> lock(_viewerMutex);
		osgViewer::Viewer viewer;
		osg::ref_ptr<osg::GraphicsContext> gc;

		viewer.setSceneData(sceneGraph);
		viewer.addEventHandler(captureHandler);
		captureHandler->startCapture();

		osg::DisplaySettings* ds = osg::DisplaySettings::instance().get();
		osg::ref_ptr<osg::GraphicsContext::Traits> traits = new osg::GraphicsContext::Traits(ds);
		traits->width = width;
		traits->height = height;
		traits->pbuffer = true;
		gc = osg::GraphicsContext::createGraphicsContext(traits.get());

		if (!gc.valid()) {
			LOG(ERROR) << "Cannot create GraphicsContext!";
			return;
		}

		GLenum pbuffer = gc->getTraits()->doubleBuffer ? GL_BACK : GL_FRONT;

		viewer.setCameraManipulator(new osgGA::TrackballManipulator());
		viewer.getCamera()->setGraphicsContext(gc.get());
		viewer.getCamera()->setViewport(new osg::Viewport(0,0,traits->width,traits->height));
		viewer.getCamera()->setDrawBuffer(pbuffer);
		viewer.getCamera()->setReadBuffer(pbuffer);

		double zoom = 1;
		CAST_PARAM(req.params, zoom, "zoom", double);

		// set background color
		viewer.getCamera()->setClearColor(osg::Vec4f(1.0f,1.0f,1.0f,1.0f));
		viewer.getCamera()->setClearMask(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
		viewer.getCameraManipulator()->setByMatrix(osg::Matrix::lookAt(osg::Vec3d(0,0,bs.radius() * (-3.4 * zoom)),  // eye
						(osg::Vec3d)bs.center(),           // center
						osg::Vec3d(0,1,0)));               // up

	//  viewer.home();

		// perform one viewer iteration
		viewer.realize();
		viewer.frame();

		viewer.removeEventHandler(captureHandler);
	}

//	delete(cOp);
//	delete(captureHandler);
}

void OSGConverter::reportSuccess(const SendRequest& req, const Data& content) {
	Event event(req);
	
	if (event.name.length() == 0)
		event.name = "convert";
	event.name += ".success";
	if (content)
		event.data.compound["content"] = content;
	returnEvent(event);
}

void OSGConverter::reportFailure(const SendRequest& req) {
	Event event(req);
	if (event.name.length() == 0)
		event.name = "convert";
	event.name += ".failure";
	returnEvent(event);
}

osg::Matrix OSGConverter::requestToModelPose(const SendRequest& req) {
	double pitch = 0;
	double roll = 0;
	double yaw = 0;
	double x = 0;
	double y = 0;
	double z = 0;
	CAST_PARAM(req.params, pitch, "pitch", double);
	CAST_PARAM(req.params, roll, "roll", double);
	CAST_PARAM(req.params, yaw, "yaw", double);
	CAST_PARAM(req.params, x, "x", double);
	CAST_PARAM(req.params, y, "y", double);
	CAST_PARAM(req.params, z, "z", double);

	osg::Matrix m = eulerToMatrix(pitch, roll, yaw) * osg::Matrix::translate(-1 * x, -1 * y, -1 * z);
#if 0
	dumpMatrix(m);
#endif
	return m;
}

osg::Matrix OSGConverter::requestToCamPose(const SendRequest& req) {
//  double zoom = 1;
//  CAST_PARAM(req.params, zoom, "zoom", double);
//  osg::Matrix scale = osg::Matrix::scale(zoom, zoom, zoom);
//  return scale;
	osg::Matrix identity;
	identity.makeIdentity();
	return identity;
}

osg::ref_ptr<osg::Node> OSGConverter::setupGraph(const std::string filename, bool autoRotate) {

	// get some privacy
	tthread::lock_guard<tthread::recursive_mutex> lock(_cacheMutex);

	/**
	 *  root (model pose)
	 *    - rotate (autoRotate to face largest side)
	 *      - modelCenter (center model)
	 *        - model (actual model)
	 */

	long now = tthread::chrono::system_clock::now();

	{

		// do we have it in the cache?
		if (_models.find(filename) == _models.end()) {
			osg::ref_ptr<osg::Node> model = osgDB::readNodeFile(filename);
			if (!model.valid()) {
				LOG(ERROR) << "Cannot load model from " << filename;
				return new osg::MatrixTransform();
			}
			_models[filename] = std::make_pair(now, model);
		}
		_models[filename].first = now;

#if 1
		// remove old models from cache
		std::map<std::string, std::pair<long, osg::ref_ptr<osg::Node> > >::iterator modelIter = _models.begin();
		while(modelIter != _models.end()) {
			// delete every model unused for 1 minutes
			if (now - modelIter->second.first > 6000) {
				_models.erase(modelIter++);
			} else {
				modelIter++;
			}
		}

#endif
	}

	osg::ref_ptr<osg::MatrixTransform> root = new osg::MatrixTransform();
	osg::ref_ptr<osg::MatrixTransform> rotate = new osg::MatrixTransform();
	osg::ref_ptr<osg::Node> model = _models[filename].second;

	// translation matrix to move model into center
	osg::ref_ptr<osg::MatrixTransform> modelCenter = new osg::MatrixTransform();
	modelCenter->addChild(model);
	rotate->addChild(modelCenter);

	// move bounding sphere center into origin
	osg::BoundingSphere bs = model->getBound();
	modelCenter->setMatrix(osg::Matrix::translate(bs.center() *= -1));

	// get bounding box
	osg::ComputeBoundsVisitor cbv;
	osg::BoundingBox& bb(cbv.getBoundingBox());
	modelCenter->accept(cbv);

	if (autoRotate) {
		double depth = bb.zMax() - bb.zMin();
		double width = bb.xMax() - bb.xMin();
		double height = bb.yMax() - bb.yMin();

		double frontArea = width * height;
		double sideArea = depth * height;
		double topArea = depth * width;

		// rotate by multiples of 90deg to face largest area
		if (frontArea < sideArea || frontArea < topArea) {
			if (sideArea < topArea) {
				// top needs to come to front -> rotate on x
				rotate->setMatrix(osg::Matrix::rotate(M_PI_2, osg::Vec3f(1.0,0,0)));
			} else {
				// side needs to come to front
				rotate->setMatrix(osg::Matrix::rotate(M_PI_2, osg::Vec3f(0,1.0,0)));
			}
		}
	}

	// add rotation to root
	root->addChild(rotate);
	return root;
}

osg::ref_ptr<osg::Node> OSGConverter::getOrigin() {
	osg::Geode* geode = new osg::Geode();
//  osg::StateSet* stateset = new osg::StateSet();
//  stateset->setMode(GL_LIGHTING, osg::StateAttribute::ON);
//  geode->setStateSet(stateset);

	geode->addDrawable(new osg::ShapeDrawable(new osg::Sphere(osg::Vec3(0.0f,0.0f,0.0f),1)));
	geode->addDrawable(new osg::ShapeDrawable(new osg::Box(osg::Vec3(10.0f,0.0f,0.0f),0.5)));
	geode->addDrawable(new osg::ShapeDrawable(new osg::Box(osg::Vec3(0.0f,10.0f,0.0f),2)));
	geode->addDrawable(new osg::ShapeDrawable(new osg::Box(osg::Vec3(0.0f,0.0f,10.0f),4)));
	//    geode->addDrawable(new osg::ShapeDrawable(new osg::Cone(osg::Vec3(4.0f,0.0f,0.0f),radius,height),hints));

	return geode;
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

void OSGConverter::dumpMatrix(const osg::Matrix& m) {
	for (int i = 0; i < 4; i++) {
		for (int j = 0; j < 4; j++) {
			std::cout << ", " << m(i, j);
		}
		std::cout << std::endl;
	}
}

void OSGConverter::NameRespectingWriteToFile::operator()(const osg::Image& image, const unsigned int context_id) {
	
	// write to memory first
	std::string format;
	if (_req.params.find("format") != _req.params.end()) {
		format = _req.params.find("format")->second.atom;
	} else {
		_converter->reportFailure(_req);
	}

	osg::ref_ptr<osgDB::ReaderWriter::Options> op = new osgDB::ReaderWriter::Options();
	//op->setOptionString("JPEG_QUALITY 75");
	//op->setOptionString("PNG_COMPRESSION 9");

	// osgDB got confused when we write to a stringstream
	std::string tempFile = URL::getTmpFilename(format);
	osgDB::writeImageFile(image, tempFile, op);
	
	char* buffer = NULL;
	size_t length = 0;
	{
		std::ifstream file(tempFile.c_str());
		
		file.seekg(0, std::ios::end);
		length = file.tellg();
		file.seekg(0, std::ios::beg);
		buffer = (char*)malloc(length);
		file.read(buffer, length);
	}
	
	remove(tempFile.c_str());
//	osg::ref_ptr<osgDB::ReaderWriter> writerFormat = osgDB::Registry::instance()->getReaderWriterForExtension(format);
//	if(!writerFormat.valid())
//		_converter->reportFailure(_req);


#if 0
	std::stringstream ssFormat;

	osgDB::ReaderWriter::WriteResult res = writerFormat->writeImage(image, ssFormat, op);
	
	if (_filename.length() > 0) {
		std::string tmpName = _filename;
		size_t pathSep = _filename.find_last_of(PATH_SEPERATOR);
		if (pathSep != std::string::npos) {
			tmpName = _filename.substr(0, pathSep) + PATH_SEPERATOR + ".tmp" + _filename.substr(pathSep + 1, _filename.length() - pathSep - 1);
		}

		{
			std::ofstream outFile(tmpName.c_str());
			outFile << ssFormat.str();
		}
		
		if (pathSep != std::string::npos) {
			int err = rename(tmpName.c_str(), _filename.c_str());
			if (err) {
				_converter->reportFailure(_req);
			}
		}
	}
#endif
	
	Data content;
	content.compound[format] = Data(buffer, length, false);

	// save image as a raw rgba as well for ffmpeg - we are using the mpb format for now
//	osg::ref_ptr<osgDB::ReaderWriter> writerRGBA = osgDB::Registry::instance()->getReaderWriterForExtension("rgba");
//	if(writerRGBA.valid()) {
//		std::stringstream ssRGBA;
//		osgDB::ReaderWriter::WriteResult res = writerRGBA->writeImage(image, ssRGBA, op);
//		content.compound["rgba"] = Data(ssRGBA.str().c_str(), ssRGBA.str().size(), false);
//	}

	_converter->reportSuccess(_req, content);
}

}