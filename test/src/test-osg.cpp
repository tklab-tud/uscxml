#include <osgDB/ReadFile>
#include <osgViewer/Viewer>

#include "uscxml/concurrency/tinythread.h"

tthread::thread* thread;
osgViewer::Viewer viewer;

void run(void* instance) {
  osg::ref_ptr<osg::Node> loadedModel = osgDB::readNodeFile("/Users/sradomski/Documents/TK/Projects/SmartVortex/Code/FE-Design/data/sv_processed/HARD_MP_VAL_000.wrl.osgb");
  viewer.setSceneData(loadedModel.get());
  
//  viewer.startThreading();
  viewer.run();
}


int main(int argc, char** argv) {
  viewer.setThreadingModel(osgViewer::ViewerBase::SingleThreaded);
  viewer.realize();
  thread = new tthread::thread(run, NULL);
  while(true) {
    tthread::this_thread::sleep_for(tthread::chrono::microseconds(1000));
//    viewer.eventTraversal();
	}
}