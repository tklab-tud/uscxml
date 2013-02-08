#ifndef OSGCONVERTER_H_W09J90F0
#define OSGCONVERTER_H_W09J90F0

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class OSGConverter : public InvokerImpl {
public:
	OSGConverter();
	virtual ~OSGConverter();
	virtual boost::shared_ptr<IOProcessorImpl> create(Interpreter* interpreter);

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

protected:
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(OSGConverter, Invoker);
#endif

}


#endif /* end of include guard: OSGCONVERTER_H_W09J90F0 */
