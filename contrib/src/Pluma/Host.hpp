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

#ifndef PLUMA_HOST_HPP
#define PLUMA_HOST_HPP

////////////////////////////////////////////////////////////
// Headers
////////////////////////////////////////////////////////////
#include <Pluma/Config.hpp>
#include <Pluma/Provider.hpp>

#include <vector>
#include <list>
#include <map>

namespace pluma{

////////////////////////////////////////////////////////////
/// \brief Manages providers.
///
////////////////////////////////////////////////////////////
class PLUMA_API Host{
friend class PluginManager;
friend class Provider;


public:

    ////////////////////////////////////////////////////////////
    /// \brief Add provider.
    ///
    /// Provider type and version are checked. Only known and
    /// valid provider types are accepted.
    ///
    /// \param provider Provider to be added.
    ///
    /// \return True if the provider is accepted.
    ///
    ////////////////////////////////////////////////////////////
    bool add(Provider* provider);


private:

    ////////////////////////////////////////////////////////////
    /// \brief Default constructor.
    ///
    /// New Host instances are not publicly allowed.
    ///
    ////////////////////////////////////////////////////////////
    Host();

    ////////////////////////////////////////////////////////////
    /// \brief Destructor.
    ///
    /// Clears all hosted providers
    ///
    ////////////////////////////////////////////////////////////
    ~Host();

    ////////////////////////////////////////////////////////////
    /// \brief Ckeck if a provider type is registered.
    ///
    /// \param type Provider type id.
    ///
    /// \return True if the type is registered
    ///
    ////////////////////////////////////////////////////////////
    bool knows(const std::string& type) const;

    ////////////////////////////////////////////////////////////
    /// \brief Get version of a type of providers.
    ///
    /// \param type Provider type.
    ///
    /// \return The version of the provider type.
    ///
    ////////////////////////////////////////////////////////////
    unsigned int getVersion(const std::string& type) const;

    ////////////////////////////////////////////////////////////
    /// \brief Get lowest compatible version of a type of providers.
    ///
    /// \param type Provider type.
    ///
    /// \return The lowest compatible version of the provider type.
    ///
    ////////////////////////////////////////////////////////////
    unsigned int getLowestVersion(const std::string& type) const;

    ////////////////////////////////////////////////////////////
    /// \brief Register a type of providers.
    ///
    /// \param type Provider type.
    /// \param version Current version of that provider type.
    /// \param lowestVersion Lowest compatible version of that provider type.
    ///
    ////////////////////////////////////////////////////////////
    void registerType(const std::string& type, unsigned int version, unsigned int lowestVersion);

    ////////////////////////////////////////////////////////////
    /// \brief Get providers of a certain type.
    ///
    /// \param type Provider type.
    ///
    /// \return Pointer to the list of providers of that \a type,
    /// or NULL if \a type is not registered.
    ///
    ////////////////////////////////////////////////////////////
    const std::list<Provider*>* getProviders(const std::string& type) const;

    ////////////////////////////////////////////////////////////
    /// \brief Clears all hosted providers.
    ///
    ////////////////////////////////////////////////////////////
    void clearProviders();

    ////////////////////////////////////////////////////////////
    /// \brief Validate provider type and version.
    ///
    /// \return True if the provider is acceptable.
    ///
    ////////////////////////////////////////////////////////////
    bool validateProvider(Provider* provider) const;

    ////////////////////////////////////////////////////////////
    /// \brief Clearly add a provider.
    ///
    /// Provider type and version are checked. Only known and
    /// valid provider types are accepted.
    /// If acepted, provider is directly stored.
    ///
    /// \param provider Provider to be added.
    ///
    /// \return True if the provider is accepted.
    ///
    ////////////////////////////////////////////////////////////
    bool registerProvider(Provider* provider);

    ////////////////////////////////////////////////////////////
    /// \brief Previous add calls are canceled.
    ///
    /// Added providers are not stored.
    ///
    /// \see add
    ///
    ////////////////////////////////////////////////////////////
    void cancelAddictions();

    ////////////////////////////////////////////////////////////
    /// \brief Previous add calls are confirmed.
    ///
    /// Added providers are finally stored.
    ///
    /// \return True if something was stored.
    ///
    /// \see add
    ///
    ////////////////////////////////////////////////////////////
    bool confirmAddictions();



////////////////////////////////////////////////////////////
// Member data
////////////////////////////////////////////////////////////

private:

    ////////////////////////////////////////////////////////////
    /// \brief Structure with information about a provider type.
    ///
    ////////////////////////////////////////////////////////////
    struct ProviderInfo{
        unsigned int version;
        unsigned int lowestVersion;
        std::list<Provider*> providers;
    };

    typedef std::map<std::string, ProviderInfo > ProvidersMap;
    typedef std::map<std::string, std::list<Provider*> > TempProvidersMap;

    ProvidersMap knownTypes;        ///< Map of registered types.
    TempProvidersMap addRequests;   ///< Temporarily added providers

};

}   // namespace pluma

#endif // PLUMA_HOST_HPP
