#ifndef COMPOSITEDISPLAY_H_W2MX9CXP
#define COMPOSITEDISPLAY_H_W2MX9CXP

#include "uscxml/concurrency/tinythread.h"
#include <osgGA/TrackballManipulator>
#include <osgViewer/Viewer>
#include <osgViewer/CompositeViewer>
#include <osgViewer/ViewerEventHandlers>
#include <osgGA/StateSetManipulator>
#include <assert.h>
#include <iostream>

class CompositeDisplay : public osgViewer::CompositeViewer {
public:
	CompositeDisplay(unsigned int x,
	                 unsigned int y,
	                 unsigned int width,
	                 unsigned int height,
	                 int screenId);
	virtual ~CompositeDisplay();

	virtual void addView(const std::string& name, osg::Viewport* v, osgViewer::View* view);
	virtual void moveView(const std::string& name, osg::Viewport* v);
	virtual void removeView(const std::string& name);

	virtual void frame(double simulationTime);
	virtual bool checkNeedToDoFrame();

	int getWidth() {
		return _width;
	}
	int getHeight() {
		return _height;
	}

	static void getResolution(unsigned int& width, unsigned int& height, int screenId);

protected:
	tthread::recursive_mutex _mutex;
	tthread::condition_variable _monitor;
	bool _waitForViewOp;
	std::map<std::string, osgViewer::View*> _views;
	std::map<std::string, osg::Viewport*> _viewports;
	osg::ref_ptr<osg::GraphicsContext> _gc;

	static osg::GraphicsContext::WindowingSystemInterface* wsi;
	int _width, _height;
};


#endif /* end of include guard: COMPOSITEDISPLAY_H_W2MX9CXP */
