#ifndef OSGINVOKER_H_H6T4R8HU
#define OSGINVOKER_H_H6T4R8HU

#include <uscxml/Interpreter.h>
#include "CompositeDisplay.h"
#include <osg/MatrixTransform>
#include <osgDB/ReadFile>
#include <set>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class OSGInvoker : public Invoker {
public:
	OSGInvoker();
	virtual ~OSGInvoker();
	virtual Invoker* create(Interpreter* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("3d");
		names.insert("scenegraph");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#3d");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(InvokeRequest& req);
	virtual void sendToParent(SendRequest& req);

  virtual void runOnMainThread();

protected:
  void processDisplay(const Arabica::DOM::Node<std::string>& element);
  void processViewport(const Arabica::DOM::Node<std::string>& element);
  void processTranslation(const Arabica::DOM::Node<std::string>& element);
  void processRotation(const Arabica::DOM::Node<std::string>& element);
  void processScale(const Arabica::DOM::Node<std::string>& element);
  void processNode(const Arabica::DOM::Node<std::string>& element);
  void processChildren(const std::set<std::string>& validChildren, const Arabica::DOM::Node<std::string>& element);
  
  void getViewport(const Arabica::DOM::Node<std::string>& element,
                   unsigned int& x,
                   unsigned int& y,
                   unsigned int& width,
                   unsigned int& height,
                   int& screenId);

  void getViewport(const Arabica::DOM::Node<std::string>& element,
                   unsigned int& x,
                   unsigned int& y,
                   unsigned int& width,
                   unsigned int& height,
                   CompositeDisplay* display);
  
  void getViewport(const Arabica::DOM::Node<std::string>& element,
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

  std::map<Arabica::DOM::Node<std::string>, osg::Node*> _nodes;
  typedef std::map<Arabica::DOM::Node<std::string>, osg::Node*> _nodes_t;

	tthread::recursive_mutex _mutex;
	std::string _invokeId;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(OSGInvoker, Invoker);
#endif

}


#endif /* end of include guard: OSGINVOKER_H_H6T4R8HU */
