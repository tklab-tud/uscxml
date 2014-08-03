/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#ifndef OSGINVOKER_H_H6T4R8HU
#define OSGINVOKER_H_H6T4R8HU

#include <uscxml/Interpreter.h>
#include <DOM/Events/MutationEvent.hpp>
#include <DOM/Events/EventListener.hpp>
#include <DOM/Events/Event.hpp>

#include "CompositeDisplay.h"
#include <osg/MatrixTransform>
#include <osg/Material>
#include <osgDB/ReadFile>

#include <set>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class OSGInvoker : public InvokerImpl, public Arabica::DOM::Events::EventListener<std::string> {
public:
	OSGInvoker();
	virtual ~OSGInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("3d");
		names.push_back("scenegraph");
		names.push_back("http://uscxml.tk.informatik.tu-darmstadt.de/#3d");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);
	virtual void handleEvent(Arabica::DOM::Events::Event<std::string>& event);

	virtual void runOnMainThread();

protected:
	void processDisplay(const Arabica::DOM::Element<std::string>& element);
	void updateDisplay(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event);
	void processViewport(const Arabica::DOM::Element<std::string>& element);
	void updateViewport(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event);
	void processCamera(const Arabica::DOM::Node<std::string>& element);
	void updateCamera(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event);

	void processTranslation(const Arabica::DOM::Element<std::string>& element);
	void updateTranslation(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event);

	void processRotation(const Arabica::DOM::Element<std::string>& element);
	void updateRotation(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event);
	static osg::Matrix rotationFromElement(const Arabica::DOM::Element<std::string>& element);

	void processScale(const Arabica::DOM::Element<std::string>& element);
	void updateScale(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event);

	void processNode(const Arabica::DOM::Element<std::string>& element);
	void updateNode(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event);

	void processSphere(const Arabica::DOM::Element<std::string>& element);
	void updateSphere(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event);
	void processBox(const Arabica::DOM::Element<std::string>& element);
	void updateBox(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event);
	void processCapsule(const Arabica::DOM::Element<std::string>& element);
	void updateCapsule(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event);
	void processCone(const Arabica::DOM::Element<std::string>& element);
	void updateCone(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event);
	void processCylinder(const Arabica::DOM::Element<std::string>& element);
	void updateCylinder(osg::ref_ptr<osg::Node> node, Arabica::DOM::Events::Event<std::string>& event);

	osg::Vec4 getColor(const Arabica::DOM::Element<std::string>& element, const std::string& attr, bool& valid);
	osg::ref_ptr<osg::Material> getMaterial(const Arabica::DOM::Element<std::string>& element);
	osg::Vec4 parseVec4(const std::string& coeffs, int& number);

	void processChildren(const std::set<std::string>& validChildren, const Arabica::DOM::Node<std::string>& element);

	void getViewport(const Arabica::DOM::Element<std::string>& element,
	                 unsigned int& x,
	                 unsigned int& y,
	                 unsigned int& width,
	                 unsigned int& height,
	                 int& screenId);

	void getViewport(const Arabica::DOM::Element<std::string>& element,
	                 unsigned int& x,
	                 unsigned int& y,
	                 unsigned int& width,
	                 unsigned int& height,
	                 CompositeDisplay* display);

	void getViewport(const Arabica::DOM::Element<std::string>& element,
	                 unsigned int& x,
	                 unsigned int& y,
	                 unsigned int& width,
	                 unsigned int& height,
	                 unsigned int fullWidth,
	                 unsigned int fullHeight);

	osgViewer::View* getView(const Arabica::DOM::Node<std::string>& element);

	std::map<Arabica::DOM::Node<std::string>, CompositeDisplay*> _displays;
	typedef std::map<Arabica::DOM::Node<std::string>, CompositeDisplay*> _displays_t;

	std::map<Arabica::DOM::Node<std::string>, osgViewer::View*> _views;
	typedef std::map<Arabica::DOM::Node<std::string>, osgViewer::View*> _views_t;

	std::map<Arabica::DOM::Node<std::string>, osg::ref_ptr<osg::Node> > _nodes;
	typedef std::map<Arabica::DOM::Node<std::string>, osg::ref_ptr<osg::Node> > _nodes_t;

	void setupColors();
	std::map<std::string, osg::Vec4> _colors;
	typedef std::map<std::string, osg::Vec4> _colors_t;

	tthread::recursive_mutex _mutex;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(OSGInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: OSGINVOKER_H_H6T4R8HU */
