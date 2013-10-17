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
