////////////////////////////////////////////////////////////
//
// Pluma - Plug-in Management Framework
// Copyright (C) 2010-2012 Gil Costa (gsaurus@gmail.com)
//
// This software is provided 'as-is', without any express or implied warranty.
// In no event will the authors be held liable for any damages arising from the use of this software.
//
// Permission is granted to anyone to use this software for any purpose,
// including commercial applications, and to alter it and redistribute it freely,
// subject to the following restrictions:
//
// 1. The origin of this software must not be misrepresented;
//    you must not claim that you wrote the original software.
//    If you use this software in a product, an acknowledgment
//    in the product documentation would be appreciated but is not required.
//
// 2. Altered source versions must be plainly marked as such,
//    and must not be misrepresented as being the original software.
//
// 3. This notice may not be removed or altered from any source distribution.
//
////////////////////////////////////////////////////////////

#ifndef PLUMA_PLUMA_HPP
#define PLUMA_PLUMA_HPP

////////////////////////////////////////////////////////////
// Headers
////////////////////////////////////////////////////////////
#include <Pluma/Config.hpp>
#include <Pluma/Provider.hpp>
#include <Pluma/PluginManager.hpp>

////////////////////////////////////////////////////////////
// Andy macro to convert parameter to string
////////////////////////////////////////////////////////////
#define PLUMA_2STRING(X) #X

////////////////////////////////////////////////////////////
// Macro that helps host applications defining
// their provider classes
////////////////////////////////////////////////////////////
#define PLUMA_PROVIDER_HEADER(TYPE)\
PLUMA_PROVIDER_HEADER_BEGIN(TYPE)\
virtual TYPE* create() const = 0;\
PLUMA_PROVIDER_HEADER_END

////////////////////////////////////////////////////////////
// Macro that generate first part of the provider definition
////////////////////////////////////////////////////////////
#define PLUMA_PROVIDER_HEADER_BEGIN(TYPE)\
class TYPE##Provider: public pluma::Provider{\
private:\
    friend class pluma::Pluma;\
    static const unsigned int PLUMA_INTERFACE_VERSION;\
    static const unsigned int PLUMA_INTERFACE_LOWEST_VERSION;\
    static const std::string PLUMA_PROVIDER_TYPE;\
    std::string plumaGetType() const{ return PLUMA_PROVIDER_TYPE; }\
public:\
    unsigned int getVersion() const{ return PLUMA_INTERFACE_VERSION; }

////////////////////////////////////////////////////////////
// Macro that generate last part of the provider definition
////////////////////////////////////////////////////////////
#define PLUMA_PROVIDER_HEADER_END };

////////////////////////////////////////////////////////////
// Macro that generate the provider declaration
////////////////////////////////////////////////////////////
#define PLUMA_PROVIDER_SOURCE(TYPE, Version, LowestVersion)\
const std::string TYPE##Provider::PLUMA_PROVIDER_TYPE = PLUMA_2STRING( TYPE );\
const unsigned int TYPE##Provider::PLUMA_INTERFACE_VERSION = Version;\
const unsigned int TYPE##Provider::PLUMA_INTERFACE_LOWEST_VERSION = LowestVersion;


////////////////////////////////////////////////////////////
// Macro that helps plugins generating their provider implementations
// PRE: SPECIALIZED_TYPE must inherit from BASE_TYPE
////////////////////////////////////////////////////////////
#define PLUMA_INHERIT_PROVIDER(SPECIALIZED_TYPE, BASE_TYPE)\
class SPECIALIZED_TYPE##Provider: public BASE_TYPE##Provider{\
public:\
    BASE_TYPE * create() const{ return new SPECIALIZED_TYPE (); }\
};


namespace pluma{

////////////////////////////////////////////////////////////
/// \brief Pluma plugins management
///
////////////////////////////////////////////////////////////
class Pluma: public PluginManager{

public:
    ////////////////////////////////////////////////////////////
    /// \brief Default Constructor
    ///
    ////////////////////////////////////////////////////////////
    Pluma();

    ////////////////////////////////////////////////////////////
    /// \brief Tell Pluma to accept a certain type of providers
    ///
    /// A Pluma object is able to accept multiple types of providers.
    /// When a plugin is loaded, it tries to register it's providers
    /// implementations. Those are only accepted by the host
    /// application if it's accepting providers of that kind.
    ///
    /// \tparam ProviderType type of provider.
    ///
    ////////////////////////////////////////////////////////////
    template<typename ProviderType>
    void acceptProviderType();

    ////////////////////////////////////////////////////////////
    /// \brief Get the stored providers of a certain type.
    ///
    /// Providers are added at the end of the \a providers vector.
    ///
    /// \tparam ProviderType type of provider to be returned.
    /// \param[out] providers Vector to fill with the existing
    /// providers.
    ///
    ////////////////////////////////////////////////////////////
    template<typename ProviderType>
    void getProviders(std::vector<ProviderType*>& providers);
};

#include <Pluma/Pluma.inl>

}


#endif // PLUMA_PLUMA_HPP


////////////////////////////////////////////////////////////
/// \class pluma::Pluma
///
/// Pluma is the main class of Pluma library. Allows hosting
/// applications to load/unload dlls in runtime (plugins), and
/// to get providers of shared interface objects.
///
/// Example:
/// \code
/// pluma::Pluma pluma;
/// // Tell it to accept providers of the type DeviceProvider
/// pluma.acceptProviderType<DeviceProvider>();
/// // Load some dll
/// pluma.load("plugins/standard_devices");
/// // Get device providers into a vector
/// std::vector<DeviceProvider*> providers;
/// pluma.getProviders(providers);
/// // create a Device from the first provider
/// if (!providers.empty()){
///     Device* myDevice = providers.first()->create();
///     // do something with myDevice
///     std::cout << device->getDescription() << std::endl;
///     // (...)
///     delete myDevice;
/// }
/// \endcode
///
/// It is also possible to add local providers, providers that
/// are defined directly on the host application. That can
/// be useful to provide and use default implementations of certain
/// interfaces, along with plugin implementations.
///
////////////////////////////////////////////////////////////
