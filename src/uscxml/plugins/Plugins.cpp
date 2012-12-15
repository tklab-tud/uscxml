#include "Plugins.h"

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_PROVIDER_SOURCE(DataModel, 1, 1);
PLUMA_PROVIDER_SOURCE(IOProcessor, 1, 1);
PLUMA_PROVIDER_SOURCE(Invoker, 1, 1);
#endif
	
}