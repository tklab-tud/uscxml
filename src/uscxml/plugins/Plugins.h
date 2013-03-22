#ifndef PLUGINS_H_M6G1NF1E
#define PLUGINS_H_M6G1NF1E

#include <Pluma/Pluma.hpp>
#include "uscxml/Factory.h"

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_PROVIDER_HEADER(IOProcessorImpl);
PLUMA_PROVIDER_HEADER(InvokerImpl);
PLUMA_PROVIDER_HEADER(ExecutableContentImpl);
PLUMA_PROVIDER_HEADER(DataModelImpl);
#endif

}

#endif /* end of include guard: PLUGINS_H_M6G1NF1E */
