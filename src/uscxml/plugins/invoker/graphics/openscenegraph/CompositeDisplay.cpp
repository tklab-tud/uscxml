#include "CompositeDisplay.h"

CompositeDisplay::CompositeDisplay(unsigned int x,
                                   unsigned int y,
                                   unsigned int width,
                                   unsigned int height,
                                   int screenId)
{
  _waitForViewOp = false;
  unsigned int tWidth = 0;
  unsigned int tHeight = 0;
  getResolution(tWidth, tHeight, screenId);
  
  osg::ref_ptr<osg::GraphicsContext::Traits> traits = new osg::GraphicsContext::Traits;
  traits->doubleBuffer = true;
  traits->sharedContext = 0;
  traits->screenNum = screenId;
  
  if (width == 0 || height == 0 || (width == tWidth && height == tHeight)) {
    // fullscreen
    traits->windowDecoration = false;
    traits->width = tWidth;
    traits->height = tHeight;
    traits->x = 0;
    traits->y = 0;    
  } else {
    // Start with given resolution
    traits->windowDecoration = true;
    traits->x = x;
    traits->y = y;
    traits->width = width;
    traits->height = height;
  }
  
  _gc = osg::GraphicsContext::createGraphicsContext(traits.get());
  if (_gc.valid()) {
    _gc->setClearColor(osg::Vec4f(1.0f,1.0f,1.0f,1.0f));
    _gc->setClearMask(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
  }
  
  _width = traits->width;
  _height = traits->height;
  
  setRunMaxFrameRate(30);
//  setRunFrameScheme(osgViewer::ViewerBase::ON_DEMAND);
  setThreadingModel(osgViewer::Viewer::AutomaticSelection);
}

CompositeDisplay::~CompositeDisplay() {}

void CompositeDisplay::frame(double simulationTime) {
  tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
  CompositeViewer::frame();
}

bool CompositeDisplay::checkNeedToDoFrame() {
  return CompositeViewer::checkNeedToDoFrame();
}

void CompositeDisplay::addView(const std::string& name, osg::Viewport* v, osgViewer::View* view) {
  tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
	_viewports[name] = v;
  
	_views[name] = view;
	_views[name]->setName(name);
  _views[name]->getCamera()->setName(name);
  _views[name]->setCameraManipulator(new osgGA::TrackballManipulator);
  
  // add the state manipulator
  osg::ref_ptr<osgGA::StateSetManipulator> statesetManipulator = new osgGA::StateSetManipulator;
  statesetManipulator->setStateSet(_views[name]->getCamera()->getOrCreateStateSet());
  _views[name]->addEventHandler( statesetManipulator.get() );

	_views[name]->addEventHandler( new osgViewer::StatsHandler );
	_views[name]->addEventHandler( new osgViewer::HelpHandler );
	_views[name]->addEventHandler( new osgViewer::WindowSizeHandler );
	_views[name]->addEventHandler( new osgViewer::ThreadingHandler );
  
  _views[name]->getCamera()->setViewport(v);
  
  // set graphic context
  _views[name]->getCamera()->setGraphicsContext(_gc.get());
  CompositeViewer::addView(_views[name]);

}

void CompositeDisplay::moveView(const std::string& name, osg::Viewport* v) {  
  tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
  const osg::GraphicsContext::Traits* traits = _gc->getTraits();
  osg::Viewport* absoluteVp = new osg::Viewport(v->x() * (traits->width/100.0),
                                                v->y() * (traits->height/100.0),
                                                v->width() * (traits->width/100.0),
                                                v->height() * (traits->height/100.0));
  _views[name]->getCamera()->setViewport(absoluteVp);
}

void CompositeDisplay::removeView(const std::string& name) {
  tthread::lock_guard<tthread::recursive_mutex> lock(_mutex);
  
  _views[name]->getCamera()->setGraphicsContext(NULL);
  _views[name]->getCamera()->setViewport(NULL);

	CompositeViewer::removeView(_views[name]);
	
	if (_views.find(name) != _views.end()) {
		_views.erase(name);
  }
	if (_viewports.find(name) != _viewports.end())
		_viewports.erase(name);
}

osg::GraphicsContext::WindowingSystemInterface* CompositeDisplay::wsi = NULL;
void CompositeDisplay::getResolution(unsigned int& width, unsigned int& height, int screenId) {
  if (!wsi)
    wsi = osg::GraphicsContext::getWindowingSystemInterface();
  wsi->getScreenResolution(osg::GraphicsContext::ScreenIdentifier(screenId), width, height);
}
