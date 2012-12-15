#ifndef PLUGINS_H_M6G1NF1E
#define PLUGINS_H_M6G1NF1E

#include <Pluma/Pluma.hpp>
#include "uscxml/Factory.h"

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_PROVIDER_HEADER(IOProcessor);
PLUMA_PROVIDER_HEADER(Invoker);
PLUMA_PROVIDER_HEADER(DataModel);
#endif

}

#endif /* end of include guard: PLUGINS_H_M6G1NF1E */
