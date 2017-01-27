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

#ifndef PLUGINS_H_M6G1NF1E
#define PLUGINS_H_M6G1NF1E

#include "uscxml/config.h"
#include <Pluma/Pluma.hpp>
#include "uscxml/plugins/DataModelImpl.h"
#include "uscxml/plugins/IOProcessorImpl.h"
#include "uscxml/plugins/InvokerImpl.h"
#include "uscxml/plugins/ExecutableContentImpl.h"

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_PROVIDER_HEADER(IOProcessorImpl)
PLUMA_PROVIDER_HEADER(InvokerImpl)
PLUMA_PROVIDER_HEADER(ExecutableContentImpl)
PLUMA_PROVIDER_HEADER(DataModelImpl)
#endif

}

#endif /* end of include guard: PLUGINS_H_M6G1NF1E */
