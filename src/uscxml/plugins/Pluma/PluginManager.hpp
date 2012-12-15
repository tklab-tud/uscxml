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

#ifndef PLUMA_PLUGIN_MANAGER_HPP
#define PLUMA_PLUGIN_MANAGER_HPP

////////////////////////////////////////////////////////////
// Headers
////////////////////////////////////////////////////////////
#include <Pluma/Config.hpp>
#include <Pluma/Host.hpp>

#include <string>
#include <map>

namespace pluma{
class DLibrary;

////////////////////////////////////////////////////////////
/// \brief Manages loaded plugins.
///
////////////////////////////////////////////////////////////
class PLUMA_API PluginManager{


public:

    ////////////////////////////////////////////////////////////
    /// \brief Destructor.
    ///
    ////////////////////////////////////////////////////////////
    ~PluginManager();

    ////////////////////////////////////////////////////////////
    /// \brief Load a plugin given it's path
    ///
    /// \param path Path for the plugin, including plugin name. File extension
    /// may be included, but is discouraged for better cross platform code.
    /// If file extension isn't present on the path, Pluma will deduce it
    /// from the operating system.
    ///
    /// \return True if the plugin is successfully loaded.
    ///
    /// \see load(const std::string&, const std::string&)
    /// \see loadFromFolder
    /// \see unload
    /// \see unloadAll
    ///
    ////////////////////////////////////////////////////////////
    bool load(const std::string& path);


    ////////////////////////////////////////////////////////////
    /// \brief Load a plugin from a given folder
    ///
    /// \param folder The folder path.
    /// \param pluginName Name of the plugin. File extension
    /// may be included, but is discouraged for better cross platform code.
    /// If file extension is omitted, Pluma will deduce it
    /// from the operating system.
    ///
    /// \return True if the plugin is successfully loaded.
    ///
    /// \see load(const std::string&)
    /// \see loadFromFolder
    /// \see unload
    /// \see unloadAll
    ///
    ////////////////////////////////////////////////////////////
    bool load(const std::string& folder, const std::string& pluginName);

    ////////////////////////////////////////////////////////////
    /// \brief Load all plugins from a given folder
    ///
    /// \param folder Path for the folder where the plug-ins are.
    /// \param recursive If true it will search on sub-folders as well
    ///
    /// \return Number of successfully loaded plug-ins.
    ///
    /// \see load(const std::string&, const std::string&)
    /// \see load(const std::string&)
    /// \see unload
    /// \see unloadAll
    ///
    ////////////////////////////////////////////////////////////
    int loadFromFolder(const std::string& folder, bool recursive = false);

    ////////////////////////////////////////////////////////////
    /// \brief Unload a plugin.
    ///
    /// \param pluginName Name or path of the plugin.
    ///
    /// \return True if the plugin is successfully unloaded,
    /// false if no such plugin exists on the manager.
    ///
    /// \see load(const std::string&, const std::string&)
    /// \see load(const std::string&)
    /// \see loadFromFolder
    /// \see unloadAll
    ///
    ////////////////////////////////////////////////////////////
    bool unload(const std::string& pluginName);

    ////////////////////////////////////////////////////////////
    /// \brief Unload all loaded plugins.
    ///
    /// \see load(const std::string&, const std::string&)
    /// \see load(const std::string&)
    /// \see loadFromFolder
    /// \see unload
    ///
    ////////////////////////////////////////////////////////////
    void unloadAll();

    ////////////////////////////////////////////////////////////
    /// \brief Directly add a new provider.
    ///
    /// \param provider Provider.
    ///
    ////////////////////////////////////////////////////////////
    bool addProvider(Provider* provider);

    ////////////////////////////////////////////////////////////
    /// \brief Get the name of all loaded plugins.
    ///
    /// \param pluginNames A vector to fill with the plugins names.
    ///
    ////////////////////////////////////////////////////////////
    void getLoadedPlugins(std::vector<const std::string*>& pluginNames) const;

    ////////////////////////////////////////////////////////////
    /// \brief Check if a plug-in is loaded.
    ///
    /// \param pluginName the plug-in tname o check.
    ///
    ////////////////////////////////////////////////////////////
    bool isLoaded(const std::string& pluginName) const;


protected:

    ////////////////////////////////////////////////////////////
    /// \brief Default constructor.
    ///
    /// PluginManager cannot be publicly instantiated.
    ///
    ////////////////////////////////////////////////////////////
    PluginManager();

    ////////////////////////////////////////////////////////////
    /// \brief Register a provider type
    ///
    /// \param type Provider type.
    /// \param version Current version of that provider type.
    /// \param lowestVersion Lowest compatible version of that provider type.
    ///
    /// \see Host::registerType
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
    /// \see Host::getProviders
    ///
    ////////////////////////////////////////////////////////////
    const std::list<Provider*>* getProviders(const std::string& type) const;


private:

    ////////////////////////////////////////////////////////////
    /// \brief Get the plugin name (without extension) from its path
    ///
    /// \param path Plugin path.
    ///
    /// \return Name of the plugin.
    ///
    /// \see resolvePathExtension
    /// \see load(const std::string&, const std::string&)
    /// \see load(const std::string&)
    /// \see unload
    ///
    ////////////////////////////////////////////////////////////
    static std::string getPluginName(const std::string& path);

    ////////////////////////////////////////////////////////////
    /// \brief If the plugin path omits it's extension, this method returns
    /// the path plus the OS specific dll extension.
    /// Return a copy of the path otherwise.
    ///
    /// \param path Plugin path.
    ///
    /// \return Path with extension.
    ///
    /// \see getPluginName
    /// \see load(const std::string&, const std::string&)
    /// \see load(const std::string&)
    /// \see unload
    ///
    ////////////////////////////////////////////////////////////
    static std::string resolvePathExtension(const std::string& path);


private:

    /// Signature for the plugin's registration function
    typedef bool fnRegisterPlugin(Host&);
    typedef std::map<std::string,DLibrary*> LibMap;

    LibMap libraries;   ///< Map containing the loaded libraries
    Host host;          ///< Host app proxy, holding all providers

};

}   // namespace pluma

#endif // PLUMA_PLUGIN_MANAGER_HPP
