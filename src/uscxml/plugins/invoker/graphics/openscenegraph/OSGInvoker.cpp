#include "OSGInvoker.h"
#include "uscxml/URL.h"
#include "uscxml/UUID.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new OSGInvokerProvider() );
	return true;
}
#endif

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
}

void OSGInvoker::cancel(const std::string sendId) {
}

void OSGInvoker::invoke(const InvokeRequest& req) {
	tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);

	// register default event handlers
	Arabica::DOM::Events::EventTarget<std::string> evTarget = Arabica::DOM::Events::EventTarget<std::string>(req.dom);
	evTarget.addEventListener("DOMSubtreeModified", *this, false);
	evTarget.addEventListener("DOMNodeInserted", *this, false);
	evTarget.addEventListener("DOMNodeRemoved", *this, false);
	evTarget.addEventListener("DOMAttrModified", *this, false);

	std::set<std::string> validChilds;
	validChilds.insert("display");
	processChildren(validChilds, req.dom);
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
		osg::Node* osgNode = _nodes[node];
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

	std::set<std::string> validChilds;
	validChilds.insert("camera");
	validChilds.insert("translation");
	validChilds.insert("rotation");
	validChilds.insert("scale");
	validChilds.insert("node");
	processChildren(validChilds, element);
}

void OSGInvoker::processCamera(const Arabica::DOM::Node<std::string>& element) {}
void OSGInvoker::updateCamera(osg::Node* node, Arabica::DOM::Events::Event<std::string>& event) {}

void OSGInvoker::processTranslation(const Arabica::DOM::Node<std::string>& element) {
	assert(_nodes.find(element.getParentNode()) != _nodes.end());
	osg::Node* node = _nodes[element.getParentNode()];

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
	processChildren(validChilds, element);
}

void OSGInvoker::processRotation(const Arabica::DOM::Node<std::string>& element) {
	assert(_nodes.find(element.getParentNode()) != _nodes.end());
	osg::Node* node = _nodes[element.getParentNode()];

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
	processChildren(validChilds, element);
}

void OSGInvoker::updateRotation(osg::Node* node, Arabica::DOM::Events::Event<std::string>& event) {
	osg::MatrixTransform* transform = static_cast<osg::MatrixTransform*>(node);
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
	osg::Node* node = _nodes[element.getParentNode()];

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
	processChildren(validChilds, element);
}

void OSGInvoker::processNode(const Arabica::DOM::Node<std::string>& element) {
	_nodes_t::iterator nodeIter = _nodes.find(element.getParentNode());
	assert(nodeIter != _nodes.end());

	assert(_nodes.find(element.getParentNode()) != _nodes.end());
	osg::Node* parent = _nodes[element.getParentNode()];

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

void OSGInvoker::processChildren(const std::set<std::string>& validChildren, const Arabica::DOM::Node<std::string>& element) {
	Arabica::DOM::NodeList<std::string> childs = element.getChildNodes();
	for (int i = 0; i < childs.getLength(); ++i) {
		if (childs.item(i).getNodeType() != Arabica::DOM::Node_base::ELEMENT_NODE)
			continue;
		if (false) {
		} else if (boost::iequals(LOCALNAME(childs.item(i)), "node") &&
		           validChildren.find("node") != validChildren.end()) {
			processNode(childs.item(i));
		} else if (boost::iequals(LOCALNAME(childs.item(i)), "translation") &&
		           validChildren.find("translation") != validChildren.end()) {
			processTranslation(childs.item(i));
		} else if (boost::iequals(LOCALNAME(childs.item(i)), "rotation") &&
		           validChildren.find("rotation") != validChildren.end()) {
			processRotation(childs.item(i));
		} else if (boost::iequals(LOCALNAME(childs.item(i)), "scale") &&
		           validChildren.find("scale") != validChildren.end()) {
			processScale(childs.item(i));
		} else if (boost::iequals(LOCALNAME(childs.item(i)), "viewport") &&
		           validChildren.find("viewport") != validChildren.end()) {
			processViewport(childs.item(i));
		} else if (boost::iequals(LOCALNAME(childs.item(i)), "camera") &&
		           validChildren.find("camera") != validChildren.end()) {
			processCamera(childs.item(i));
		} else if (boost::iequals(LOCALNAME(childs.item(i)), "display") &&
		           validChildren.find("display") != validChildren.end()) {
			processDisplay(childs.item(i));
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