#include "Plugins.h"

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_PROVIDER_SOURCE(DataModelImpl, 1, 1);
PLUMA_PROVIDER_SOURCE(IOProcessorImpl, 1, 1);
PLUMA_PROVIDER_SOURCE(InvokerImpl, 1, 1);
PLUMA_PROVIDER_SOURCE(ElementImpl, 1, 1);
#endif

}