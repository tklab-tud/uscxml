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

#ifndef PLUMA_PROVIDER_HPP
#define PLUMA_PROVIDER_HPP

////////////////////////////////////////////////////////////
// Headers
////////////////////////////////////////////////////////////
#include <Pluma/Config.hpp>
#include <string>


namespace pluma{
class Host;

////////////////////////////////////////////////////////////
/// \brief Interface to provide applications with objects from plugins.
///
////////////////////////////////////////////////////////////
class PLUMA_API Provider{
friend class Host;


public:

    ////////////////////////////////////////////////////////////
    /// \brief Destructor.
    ///
    ////////////////////////////////////////////////////////////
    virtual ~Provider();

    ////////////////////////////////////////////////////////////
    /// \brief Get provider version.
    ///
    /// \return Version number.
    ///
    ////////////////////////////////////////////////////////////
    virtual unsigned int getVersion() const = 0;

    ////////////////////////////////////////////////////////////
    /// \brief Check compatibility with host.
    ///
    /// The same provider may be compiled with different versions
    /// on host side and on plugins side. This function checks if
    /// a plugin provider is compatible with the current version of
    /// the same provider type on the host side.
    ///
    /// \param host Host, proxy of host application.
    ///
    /// \return True if it's compatible with \a host.
    ///
    ////////////////////////////////////////////////////////////
    bool isCompatible(const Host& host) const;


private:

    ////////////////////////////////////////////////////////////
    /// \brief Get provider type.
    ///
    /// Each provider defined on the host application is identified by
    /// a unique type. Those types are automatically managed internally by
    /// pluma.
    ///
    /// \return Provider type id.
    ///
    ////////////////////////////////////////////////////////////
    virtual std::string plumaGetType() const = 0;

};

}   // namespace pluma


#endif // PLUMA_PROVIDER_HPP


////////////////////////////////////////////////////////////
/// \class pluma::Provider
/// The plugin specific implementations are unknown at the host side,
/// only their shared interfaces are known. Then, host app needs a generic
/// way of create interface objects. That's what provider classes are for.
/// It is the factory design pattern
/// (http://www.oodesign.com/factory-pattern.html)
///
/// Shared interfaces define their provider types (by inheriting from
/// pluma::Provider). Hosts then use those tipes to get objects from the
/// plugins.
/// Plugins derive the shared interface providers so that they can provide
/// host with specific implementations of the shared interface.
/// Those specific providers are given to the host through a connect function.
///
///
/// Example: A host app uses objects of type Device. A certain plugin
/// defines a Keyboard, witch is a Device.
/// The Host will use DeviceProviders to create objects of type Device.
/// The plugin will provide host specifically with a KeyboardProvider.
/// Other plugins may provide host with other derived DeviceProvider types.
///
/// Device hpp (shared):
/// \code
/// #include <Pluma/Pluma.hpp>
/// class Device{
/// public:
///     virtual std::string getDescription() const = 0;
/// };
/// // create DevicedProvider class
/// PLUMA_PROVIDER_HEADER(Device);
/// \endcode
///
/// Device cpp (shared):
/// \code
/// #include "Device.hpp"
/// generate DevicedProvider with version 6, and compatible with at least v.3
/// PLUMA_PROVIDER_SOURCE(Device, 6, 3);
/// \endcode
///
///
/// <br>
/// Keyboard code on the plugin side:
/// \code
/// #include <Pluma/Pluma.hpp>
/// #include "Device.hpp"
///
/// class Keyboard: public Device{
/// public:
///     std::string getDescription() const{
///         return "keyboard";
///     }
/// };
///
/// // create KeyboardProvider, it implements DeviceProvider
/// PLUMA_INHERIT_PROVIDER(Keyboard, Device);
/// \endcode
///
/// plugin connector:
/// \code
/// #include <Pluma/Connector.hpp>
/// #include "Keyboard.hpp"
///
/// PLUMA_CONNECTOR
/// bool connect(pluma::Host& host){
///     // add a keyboard provider to host
///     host.add( new KeyboardProvider() );
///     return true;
/// }
/// \endcode
///
///
/// Host application code:
/// \code
/// #include <Pluma/Pluma.hpp>
///
/// #include "Device.hpp"
/// #include <iostream>
/// #include <vector>
///
/// int main(){
///
///     pluma::Pluma plugins;
///     // Tell plugins manager to accept providers of the type DeviceProvider
///     plugins.acceptProviderType<DeviceProvider>();
///     // Load library "standard_devices" from folder "plugins"
///     plugins.load("plugins", "standard_devices");
///
///     // Get device providers into a vector
///     std::vector<DeviceProvider*> providers;
///     plugins.getProviders(providers);
///
///     // create a Device from the first provider
///     if (!providers.empty()){
///         Device* myDevice = providers.first()->create();
///         // do something with myDevice
///         std::cout << device->getDescription() << std::endl;
///         // and delete it in the end
///         delete myDevice;
///     }
///     return 0;
/// }
/// \endcode
///
////////////////////////////////////////////////////////////
