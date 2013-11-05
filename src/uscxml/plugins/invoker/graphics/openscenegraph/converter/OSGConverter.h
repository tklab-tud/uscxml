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

#ifndef OSGCONVERTER_H_W09J90F0
#define OSGCONVERTER_H_W09J90F0

#include <uscxml/Interpreter.h>
#include <osg/Node>
#include <osgViewer/ViewerEventHandlers>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class OSGConverter : public InvokerImpl {
public:
	OSGConverter();
	virtual ~OSGConverter();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::set<std::string> getNames() {
		std::set<std::string> names;
		names.insert("osgconverter");
		names.insert("osgconvert");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#osgconverter");
		names.insert("http://uscxml.tk.informatik.tu-darmstadt.de/#osgconvert");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

	void reportSuccess(const SendRequest& req, const Data& content);
	void reportFailure(const SendRequest& req);

	osg::Matrix requestToModelPose(const SendRequest& req);
	osg::Matrix requestToCamPose(const SendRequest& req);

	static void dumpMatrix(const osg::Matrix& m);
	static osg::Matrix eulerToMatrix(double pitch, double roll, double yaw);
	static void matrixToEuler(const osg::Matrix& m, double& pitch, double& roll, double& yaw);

protected:

	uscxml::concurrency::BlockingQueue<SendRequest> _workQueue;
	osg::ref_ptr<osg::Node> setupGraph(const std::string filename, bool autoRotate = false);
	osg::ref_ptr<osg::Node> getOrigin();

	tthread::recursive_mutex _viewerMutex;

	std::map<std::string, std::pair<long, osg::ref_ptr<osg::Node> > > _models;
	tthread::recursive_mutex _cacheMutex;

	std::set<tthread::thread*> _threads;

	static void run(void*);
	void process(const SendRequest& req);

	bool _isRunning;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(OSGConverter, InvokerImpl);
#endif

}


#endif /* end of include guard: OSGCONVERTER_H_W09J90F0 */
