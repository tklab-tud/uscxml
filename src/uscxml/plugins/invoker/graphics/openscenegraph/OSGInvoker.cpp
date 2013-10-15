#include "OSGInvoker.h"
#include "uscxml/URL.h"
#include "uscxml/UUID.h"
#include <glog/logging.h>

#include <osg/Shape>
#include <osg/ShapeDrawable>
#include <osg/Material>
#include <osg/Depth>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#define OSG_SET_MATERIAL \
osg::ref_ptr<osg::Material> mat = getMaterial(element); \
if (mat) { \
	osg::ref_ptr<osg::StateSet> nodeSS = geode->getOrCreateStateSet(); \
\
	nodeSS->setAttribute(mat.get()); \
	nodeSS->setMode( GL_BLEND, osg::StateAttribute::ON ); \
/*	nodeSS->setRenderingHint( osg::StateSet::TRANSPARENT_BIN ); \
	nodeSS->setMode( GL_DEPTH_TEST, osg::StateAttribute::ON ); \
	osg::Depth* depth = new osg::Depth; \
	depth->setWriteMask( false ); \
	nodeSS->setAttributeAndModes( depth, osg::StateAttribute::ON ); \
	nodeSS->setMode( GL_LIGHTING, osg::StateAttribute::OFF );*/ \
}

#define OSG_SET_COLOR \
bool validColor = true; \
osg::Vec4 color = getColor(element, "color", validColor); \
if (validColor) \
drawable->setColor(color);

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new OSGInvokerProvider() );
	return true;
}
#endif

#define OSG_TAG_HANDLE(tagName, procFunc) \
} else if (boost::iequals(LOCALNAME(childs.item(i)), tagName) && \
	validChildren.find(tagName) != validChildren.end()) { \
		procFunc(childs.item(i));\

	
OSGInvoker::OSGInvoker() {
}

OSGInvoker::~OSGInvoker() {
};

boost::shared_ptr<InvokerImpl> OSGInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<OSGInvoker> invoker = boost::shared_ptr<OSGInvoker> (new OSGInvoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

Data OSGInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void OSGInvoker::send(const SendRequest& req) {
	if (boost::iequals(req.name, "intersect")) {
		
	}
}

void OSGInvoker::cancel(const std::string sendId) {
}

void OSGInvoker::invoke(const InvokeRequest& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	setupColors();
	
	std::cout << req.dom;
	
	// register default event handlers
	Arabica::DOM::Events::EventTarget<std::string> evTarget = Arabica::DOM::Events::EventTarget<std::string>(req.dom);
	evTarget.addEventListener("DOMSubtreeModified", *this, false);
	evTarget.addEventListener("DOMNodeInserted", *this, false);
	evTarget.addEventListener("DOMNodeRemoved", *this, false);
	evTarget.addEventListener("DOMAttrModified", *this, false);

	std::set<std::string> validChilds;
	validChilds.insert("display");
	
	// this is somewhat unfortunate, if content contains a single child, we will get that, otherwise its parent (<content>)
	if (boost::iequals(LOCALNAME(req.dom), "display")) {
		processChildren(validChilds, req.dom.getParentNode());
	} else {
		processChildren(validChilds, req.dom);
	}
}

void OSGInvoker::setupColors() {
	_colors["red"] =        osg::Vec4(1.0,    0.0,    0.0,    1.0);
	_colors["cyan"] =       osg::Vec4(0.0,    1.0,    1.0,    1.0);
	_colors["blue"] =       osg::Vec4(0.0,    0.0,    1.0,    1.0);
	_colors["darkblue"] =   osg::Vec4(0.0,    0.0,    0.625,  1.0);
	_colors["lightblue"] =  osg::Vec4(0.675,  0.84375,0.89844,1.0);
	_colors["purple"] =     osg::Vec4(0.5,    0.0,    0.5,    1.0);
	_colors["yellow"] =     osg::Vec4(1.0,    1.0,    0.0,    1.0);
	_colors["lime"] =       osg::Vec4(0.0,    1.0,    0.0,    1.0);
	_colors["magenta"] =    osg::Vec4(1.0,    0.0,    1.0,    1.0);
	_colors["white"] =      osg::Vec4(1.0,    1.0,    1.0,    1.0);
	_colors["silver"] =     osg::Vec4(0.75,   0.75,   0.75,   1.0);
	_colors["grey"] =       osg::Vec4(0.5,    0.5,    0.5,    1.0);
	_colors["gray"] =       osg::Vec4(0.5,    0.5,    0.5,    1.0);
	_colors["black"] =      osg::Vec4(0.0,    0.0,    0.0,    1.0);
	_colors["orange"] =     osg::Vec4(1.0,    0.644,  0.0,    1.0);
	_colors["brown"] =      osg::Vec4(0.644,  0.164,  0.164,  1.0);
	_colors["maroon"] =     osg::Vec4(0.5,    0.0,    0.0,    1.0);
	_colors["green"] =      osg::Vec4(0.0,    0.5,    0.0,    1.0);
	_colors["olive"] =      osg::Vec4(0.5,    0.5,    0.0,    1.0);
}
	
void OSGInvoker::runOnMainThread() {
	_displays_t::iterator dispIter = _displays.begin();
	if (_mutex.try_lock()) {
		while(dispIter != _displays.end()) {
			dispIter->second->osgViewer::ViewerBase::frame();
			dispIter++;
		}
		_mutex.unlock();
	}
}

void OSGInvoker::handleEvent(Arabica::DOM::Events::Event<std::string>& event) {
//  std::cout << "Handling Event!" << std::endl;
	Arabica::DOM::Node<std::string> node(event.getTarget());
	if (_nodes.find(node) != _nodes.end()) {
		osg::ref_ptr<osg::Node> osgNode = _nodes[node];
		if (false) {
		} else if (boost::iequals(LOCALNAME(node), "rotation")) {
			updateRotation(osgNode, event);
		}
	}
}

void OSGInvoker::processDisplay(const Arabica::DOM::Node<std::string>& element) {
//  std::cout << element << std::endl;

	if (_displays.find(element) == _displays.end()) {

		int screenId = 0;
		unsigned int actualX = 0;
		unsigned int actualY = 0;
		unsigned int actualWidth = 0;
		unsigned int actualHeight = 0;
		getViewport(element, actualX, actualY, actualWidth, actualHeight, screenId);

		CompositeDisplay* compDisp = new CompositeDisplay(actualX, actualY, actualWidth, actualHeight, screenId);
		_displays[element] = compDisp;

		std::set<std::string> validChilds;
		validChilds.insert("viewport");
		processChildren(validChilds, element);
	}
}

void OSGInvoker::processViewport(const Arabica::DOM::Node<std::string>& element) {
	if (_displays.find(element.getParentNode()) == _displays.end())
		return;

	CompositeDisplay* compDisp = _displays[element.getParentNode()];
	osgViewer::View* sceneView = new osgViewer::View();
	_views[element] = sceneView;

	osg::Group* group = new osg::Group();
	_nodes[element] = group;
	sceneView->setSceneData(group);

	std::string name = (HAS_ATTR(element, "id") ? ATTR(element, "id") : UUID::getUUID());

	unsigned int actualX = 0;
	unsigned int actualY = 0;
	unsigned int actualWidth = 0;
	unsigned int actualHeight = 0;
	
	getViewport(element, actualX, actualY, actualWidth, actualHeight, compDisp);
	osg::Viewport* viewPort = new osg::Viewport(actualX, actualY, actualWidth, actualHeight);
	compDisp->addView(name, viewPort, sceneView);

	bool hasBGColor;
	osg::Vec4 bgColor = getColor(element, "bgcolor", hasBGColor);
	if (hasBGColor) {
		sceneView->getCamera()->setClearColor(bgColor);
	} else {
		sceneView->getCamera()->setClearColor(_colors["white"]);
	}
	
	std::set<std::string> validChilds;
	validChilds.insert("camera");
	validChilds.insert("translation");
	validChilds.insert("rotation");
	validChilds.insert("scale");
	validChilds.insert("node");
	validChilds.insert("sphere");
	validChilds.insert("box");
	validChilds.insert("capsule");
	validChilds.insert("cone");
	validChilds.insert("cylinder");
	processChildren(validChilds, element);
}

void OSGInvoker::processCamera(const Arabica::DOM::Node<std::string>& element) {}
void OSGInvoker::updateCamera(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event) {}

void OSGInvoker::processTranslation(const Arabica::DOM::Node<std::string>& element) {
	assert(_nodes.find(element.getParentNode()) != _nodes.end());
	osg::ref_ptr<osg::Node> node = _nodes[element.getParentNode()];

	double x = 0, y = 0, z = 0;
	if (HAS_ATTR(element, "x"))
		x = strTo<float>(ATTR(element, "x"));
	if (HAS_ATTR(element, "y"))
		y = strTo<float>(ATTR(element, "y"));
	if (HAS_ATTR(element, "z"))
		z = strTo<float>(ATTR(element, "z"));

	osg::Matrix translate;
	translate.makeTranslate(x, y, z);

	osg::MatrixTransform* transform = new osg::MatrixTransform();
	transform->setMatrix(translate);
	node->asGroup()->addChild(transform);
	_nodes[element] = transform;

	std::set<std::string> validChilds;
	validChilds.insert("translation");
	validChilds.insert("rotation");
	validChilds.insert("scale");
	validChilds.insert("node");
	validChilds.insert("sphere");
	validChilds.insert("box");
	validChilds.insert("capsule");
	validChilds.insert("cone");
	validChilds.insert("cylinder");
	processChildren(validChilds, element);
}

void OSGInvoker::processRotation(const Arabica::DOM::Node<std::string>& element) {
	assert(_nodes.find(element.getParentNode()) != _nodes.end());
	osg::ref_ptr<osg::Node> node = _nodes[element.getParentNode()];

	osg::Matrix rotation = rotationFromElement(element);
	osg::MatrixTransform* transform = new osg::MatrixTransform();
	transform->setMatrix(rotation);
	node->asGroup()->addChild(transform);
	_nodes[element] = transform;

	std::set<std::string> validChilds;
	validChilds.insert("translation");
	validChilds.insert("rotation");
	validChilds.insert("scale");
	validChilds.insert("node");
	validChilds.insert("sphere");
	validChilds.insert("box");
	validChilds.insert("capsule");
	validChilds.insert("cone");
	validChilds.insert("cylinder");
	processChildren(validChilds, element);
}

void OSGInvoker::updateRotation(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event) {
	osg::ref_ptr<osg::MatrixTransform> transform = static_cast<osg::MatrixTransform*>(node->asTransform());
	if (false) {
	} else if (boost::iequals(event.getType(), "DOMAttrModified")) {
		osg::Matrix rotation = rotationFromElement(Arabica::DOM::Node<std::string>(event.getTarget()));
		transform->setMatrix(rotation);
	}
}

osg::Matrix OSGInvoker::rotationFromElement(const Arabica::DOM::Node<std::string>& element) {
	double pitch = 0, roll = 0, yaw = 0;
	if (HAS_ATTR(element, "pitch")) {
		NumAttr pitchAttr = NumAttr(ATTR(element, "pitch"));
		if (boost::iequals(pitchAttr.unit, "deg")) {
			pitch = osg::DegreesToRadians(strTo<float>(pitchAttr.value));
		} else if (boost::iequals(pitchAttr.unit, "%")) {
			pitch = osg::DegreesToRadians((strTo<float>(pitchAttr.value) * 360) / 100);
		} else {
			pitch = strTo<float>(pitchAttr.value);
		}
	}
	if (HAS_ATTR(element, "roll")) {
		NumAttr rollAttr = NumAttr(ATTR(element, "roll"));
		if (boost::iequals(rollAttr.unit, "deg")) {
			roll = osg::DegreesToRadians(strTo<float>(rollAttr.value));
		} else if (boost::iequals(rollAttr.unit, "%")) {
			roll = osg::DegreesToRadians((strTo<float>(rollAttr.value) * 360) / 100);
		} else {
			roll = strTo<float>(rollAttr.value);
		}
	}
	if (HAS_ATTR(element, "yaw")) {
		NumAttr yawAttr = NumAttr(ATTR(element, "yaw"));
		if (boost::iequals(yawAttr.unit, "deg")) {
			yaw = osg::DegreesToRadians(strTo<float>(yawAttr.value));
		} else if (boost::iequals(yawAttr.unit, "%")) {
			yaw = osg::DegreesToRadians((strTo<float>(yawAttr.value) * 360) / 100);
		} else {
			yaw = strTo<float>(yawAttr.value);
		}
	}

	osg::Matrix rotation;
	rotation.makeRotate(roll, osg::Vec3(0,1,0), // roll
	                    pitch, osg::Vec3(1,0,0) , // pitch
	                    yaw, osg::Vec3(0,0,1) ); // heading

	return rotation;
}

void OSGInvoker::processScale(const Arabica::DOM::Node<std::string>& element) {
	assert(_nodes.find(element.getParentNode()) != _nodes.end());
	osg::ref_ptr<osg::Node> node = _nodes[element.getParentNode()];

	double x = 1, y = 1, z = 1;
	if (HAS_ATTR(element, "x"))
		x = strTo<float>(ATTR(element, "x"));
	if (HAS_ATTR(element, "y"))
		y = strTo<float>(ATTR(element, "y"));
	if (HAS_ATTR(element, "z"))
		z = strTo<float>(ATTR(element, "z"));

	osg::Matrix scale;
	scale.makeScale(x, y, z);

	osg::MatrixTransform* transform = new osg::MatrixTransform();
	transform->setMatrix(scale);
	node->asGroup()->addChild(transform);
	_nodes[element] = transform;

	std::set<std::string> validChilds;
	validChilds.insert("translation");
	validChilds.insert("rotation");
	validChilds.insert("scale");
	validChilds.insert("node");
	validChilds.insert("sphere");
	validChilds.insert("box");
	validChilds.insert("capsule");
	validChilds.insert("cone");
	validChilds.insert("cylinder");
	processChildren(validChilds, element);
}

void OSGInvoker::processNode(const Arabica::DOM::Node<std::string>& element) {
	_nodes_t::iterator nodeIter = _nodes.find(element.getParentNode());
	assert(nodeIter != _nodes.end());

	assert(_nodes.find(element.getParentNode()) != _nodes.end());
	osg::ref_ptr<osg::Node> parent = _nodes[element.getParentNode()];

	std::string filename;
	if (HAS_ATTR(element, "src")) {
		filename = ATTR(element, "src");

		if (filename.length() > 0) {
			std::string extension;
			size_t extensionStart = filename.find_last_of(".");
			if (extensionStart != std::string::npos) {
				extension = filename.substr(extensionStart);
			}

			URL srcURI(filename);
			if (!srcURI.toAbsolute(_interpreter->getBaseURI())) {
				LOG(ERROR) << "invoke element has relative src URI with no baseURI set.";
				return;
			}
			filename = srcURI.asLocalFile(extension);
			osg::ref_ptr<osg::Node> model = osgDB::readNodeFile(filename);
			if (model.get())
				parent->asGroup()->addChild(model);

		}
	}
}

void OSGInvoker::processSphere(const Arabica::DOM::Node<std::string>& element) {
	assert(_nodes.find(element.getParentNode()) != _nodes.end());
	osg::ref_ptr<osg::Node> parent = _nodes[element.getParentNode()];

	float radius = 1;
	osg::Vec3 center(0,0,0);
	
	if (HAS_ATTR(element, "radius")) {
		radius = strTo<float>(ATTR(element, "radius"));
	}
	
	osg::ref_ptr<osg::Sphere> sphere = new osg::Sphere(center, radius);
	osg::ref_ptr<osg::ShapeDrawable> drawable = new osg::ShapeDrawable(sphere);
	osg::ref_ptr<osg::Geode> geode = new osg::Geode();
	geode->addDrawable(drawable);

	OSG_SET_COLOR;
	OSG_SET_MATERIAL;

	_nodes[element] = geode;

	parent->asGroup()->addChild(geode);
}

void OSGInvoker::updateSphere(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event) {
}

void OSGInvoker::processBox(const Arabica::DOM::Node<std::string>& element) {
	assert(_nodes.find(element.getParentNode()) != _nodes.end());
	osg::ref_ptr<osg::Node> parent = _nodes[element.getParentNode()];
	
	float x = 1;
	float y = 1;
	float z = 1;
	osg::Vec3 center(0,0,0);
	
	if (HAS_ATTR(element, "x")) x = strTo<float>(ATTR(element, "x"));
	if (HAS_ATTR(element, "y")) y = strTo<float>(ATTR(element, "y"));
	if (HAS_ATTR(element, "z")) z = strTo<float>(ATTR(element, "z"));
	
	osg::ref_ptr<osg::Box> box = new osg::Box(center, x, y, z);
	osg::ref_ptr<osg::ShapeDrawable> drawable = new osg::ShapeDrawable(box);
	osg::ref_ptr<osg::Geode> geode = new osg::Geode();
	geode->addDrawable(drawable);
	
	OSG_SET_COLOR;
	OSG_SET_MATERIAL;

	_nodes[element] = geode;
	
	parent->asGroup()->addChild(geode);

}
void OSGInvoker::updateBox(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event) {
}
void OSGInvoker::processCapsule(const Arabica::DOM::Node<std::string>& element) {
	assert(_nodes.find(element.getParentNode()) != _nodes.end());
	osg::ref_ptr<osg::Node> parent = _nodes[element.getParentNode()];
	
	float radius = 1;
	float height = 1;
	osg::Vec3 center(0,0,0);
	
	if (HAS_ATTR(element, "radius")) radius = strTo<float>(ATTR(element, "radius"));
	if (HAS_ATTR(element, "height")) height = strTo<float>(ATTR(element, "height"));
	
	osg::ref_ptr<osg::Capsule> capsule = new osg::Capsule(center, radius, height);
	osg::ref_ptr<osg::ShapeDrawable> drawable = new osg::ShapeDrawable(capsule);
	osg::ref_ptr<osg::Geode> geode = new osg::Geode();
	geode->addDrawable(drawable);
	
	OSG_SET_COLOR;
	OSG_SET_MATERIAL;

	_nodes[element] = geode;
	parent->asGroup()->addChild(geode);
}
void OSGInvoker::updateCapsule(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event) {
}
	
void OSGInvoker::processCone(const Arabica::DOM::Node<std::string>& element) {
	assert(_nodes.find(element.getParentNode()) != _nodes.end());
	osg::ref_ptr<osg::Node> parent = _nodes[element.getParentNode()];
	
	float radius = 1;
	float height = 1;
	osg::Vec3 center(0,0,0);
	
	if (HAS_ATTR(element, "radius")) radius = strTo<float>(ATTR(element, "radius"));
	if (HAS_ATTR(element, "height")) height = strTo<float>(ATTR(element, "height"));
	
	osg::ref_ptr<osg::Cone> cone = new osg::Cone(center, radius, height);
	osg::ref_ptr<osg::ShapeDrawable> drawable = new osg::ShapeDrawable(cone);
	osg::ref_ptr<osg::Geode> geode = new osg::Geode();
	geode->addDrawable(drawable);
	
	OSG_SET_COLOR;
	OSG_SET_MATERIAL;

	_nodes[element] = geode;
	
	parent->asGroup()->addChild(geode);

}
void OSGInvoker::updateCone(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event) {
}

void OSGInvoker::processCylinder(const Arabica::DOM::Node<std::string>& element) {
	assert(_nodes.find(element.getParentNode()) != _nodes.end());
	osg::ref_ptr<osg::Node> parent = _nodes[element.getParentNode()];
	
	float radius = 1;
	float height = 1;
	osg::Vec3 center(0,0,0);
	
	if (HAS_ATTR(element, "radius")) radius = strTo<float>(ATTR(element, "radius"));
	if (HAS_ATTR(element, "height")) height = strTo<float>(ATTR(element, "height"));
	
	osg::ref_ptr<osg::Cylinder> cylinder = new osg::Cylinder(center, radius, height);
	osg::ref_ptr<osg::ShapeDrawable> drawable = new osg::ShapeDrawable(cylinder);
	osg::ref_ptr<osg::Geode> geode = new osg::Geode();
	geode->addDrawable(drawable);
	
	OSG_SET_COLOR;
	OSG_SET_MATERIAL;

	_nodes[element] = geode;
	
	parent->asGroup()->addChild(geode);

}
void OSGInvoker::updateCylinder(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event) {
}

osg::Vec4 OSGInvoker::getColor(const Arabica::DOM::Node<std::string>& element, const std::string& attr, bool& valid) {
	if (HAS_ATTR(element, attr)) {
		std::string color = ATTR(element, attr);

		// is this one of the predefined colors?
		if (_colors.find(color) != _colors.end()) {
			valid = true;
			return _colors[color];
		}
		
		// otherwise try to parse as rgba values
		int i;
		osg::Vec4 colorVec = parseVec4(color, i);
		
		if (i == 1) {
			// only a single value was given, interpret as grey value
			colorVec[1] = colorVec[2] = colorVec[0]; colorVec[3] = 1.0;
			valid = true;
			return colorVec;
		}

		if (i == 3) {
			// three values were given, set opacity to max
			colorVec[3] = 1.0;
			valid = true;
			return colorVec;
		}
	}
	
	// return empty reference
	valid = false;
	return osg::Vec4();
}

osg::ref_ptr<osg::Material> OSGInvoker::getMaterial(const Arabica::DOM::Node<std::string>& element) {

	osg::ref_ptr<osg::Material> nodeMat;

	// material color
	bool hasMatColor;
	osg::Vec4 matColor = getColor(element, "materialcolor", hasMatColor);
	if (hasMatColor) {
		if (!nodeMat)
			nodeMat = new osg::Material;
		nodeMat->setDiffuse(osg::Material::FRONT, matColor);
		nodeMat->setDiffuse(osg::Material::BACK, matColor);
	}
	
	// translucency
	if (HAS_ATTR(element, "transparency")) {
		std::string transparency = ATTR(element, "transparency");
		float trans = strTo<float>(transparency);
		if (!nodeMat)
			nodeMat = new osg::Material;
		nodeMat->setTransparency(osg::Material::FRONT, trans);
		nodeMat->setTransparency(osg::Material::BACK, trans);
	}
	
	return nodeMat;
}

osg::Vec4 OSGInvoker::parseVec4(const std::string& coeffs, int& i) {
	
	// otherwise try to parse as rgba values
	std::string coeff;
	std::stringstream coeffSS(coeffs);
	
	osg::Vec4 vec;
	
	i = 0;
	while(std::getline(coeffSS, coeff, ',')) {
		boost::trim(coeff);
		if (coeff.length() == 0)
			continue;
		if (!isNumeric(coeff.c_str(), 10))
			continue;
		
		vec[i] = strTo<float>(coeff);
		i++;
	}
	return vec;
}
	
void OSGInvoker::processChildren(const std::set<std::string>& validChildren, const Arabica::DOM::Node<std::string>& element) {
	Arabica::DOM::NodeList<std::string> childs = element.getChildNodes();
	for (int i = 0; i < childs.getLength(); ++i) {
		if (childs.item(i).getNodeType() != Arabica::DOM::Node_base::ELEMENT_NODE)
			continue;
		if (false) {
			OSG_TAG_HANDLE("node", processNode);
			OSG_TAG_HANDLE("translation", processTranslation);
			OSG_TAG_HANDLE("rotation", processRotation);
			OSG_TAG_HANDLE("scale", processScale);
			OSG_TAG_HANDLE("viewport", processViewport);
			OSG_TAG_HANDLE("camera", processCamera);
			OSG_TAG_HANDLE("display", processDisplay);
			OSG_TAG_HANDLE("sphere", processSphere);
			OSG_TAG_HANDLE("box", processBox);
			OSG_TAG_HANDLE("cone", processCone);
			OSG_TAG_HANDLE("capsule", processCapsule);
			OSG_TAG_HANDLE("cylinder", processCylinder);
		} else {
			LOG(INFO) << "Unknown XML element " << TAGNAME(childs.item(i));
		}
	}
}

void OSGInvoker::getViewport(const Arabica::DOM::Node<std::string>& element,
                             unsigned int& x,
                             unsigned int& y,
                             unsigned int& width,
                             unsigned int& height,
                             CompositeDisplay* display) {
	getViewport(element, x, y, width, height, display->getWidth(), display->getHeight());

}

void OSGInvoker::getViewport(const Arabica::DOM::Node<std::string>& element,
                             unsigned int& x,
                             unsigned int& y,
                             unsigned int& width,
                             unsigned int& height,
                             int& screenId) {

	screenId = (HAS_ATTR(element, "screenId") ? strTo<int>(ATTR(element, "screenId")) : 0);

	unsigned int fullWidth = 0;
	unsigned int fullHeight = 0;
	CompositeDisplay::getResolution(fullWidth, fullHeight, screenId);
	getViewport(element, x, y, width, height, fullWidth, fullHeight);
}

void OSGInvoker::getViewport(const Arabica::DOM::Node<std::string>& element,
                             unsigned int& x,
                             unsigned int& y,
                             unsigned int& width,
                             unsigned int& height,
                             unsigned int fullWidth,
                             unsigned int fullHeight) {
	if (HAS_ATTR(element, "x")) {
		NumAttr xAttr = NumAttr(ATTR(element, "x"));
		x = strTo<float>(xAttr.value);
		if (boost::iequals(xAttr.unit, "%"))
			x = (x * fullWidth) / 100;
	}
	if (HAS_ATTR(element, "y")) {
		NumAttr yAttr = NumAttr(ATTR(element, "y"));
		y = strTo<float>(yAttr.value);
		if (boost::iequals(yAttr.unit, "%"))
			y = (y * fullHeight) / 100;
	}
	if (HAS_ATTR(element, "width")) {
		NumAttr widthAttr = NumAttr(ATTR(element, "width"));
		width = strTo<float>(widthAttr.value);
		if (boost::iequals(widthAttr.unit, "%"))
			width = (width * fullWidth) / 100;
	}
	if (HAS_ATTR(element, "height")) {
		NumAttr heightAttr = NumAttr(ATTR(element, "height"));
		height = strTo<float>(heightAttr.value);
		if (boost::iequals(heightAttr.unit, "%"))
			height = (height * fullHeight) / 100;
	}
}

osgViewer::View* OSGInvoker::getView(const Arabica::DOM::Node<std::string>& element) {
	Arabica::DOM::Node<std::string> curr = element;
	while(curr && !boost::iequals(LOCALNAME(curr), "viewport")) {
		curr = curr.getParentNode();
	}
	if (curr && _views.find(curr) != _views.end())
		return _views[curr];
	return NULL;
}


}