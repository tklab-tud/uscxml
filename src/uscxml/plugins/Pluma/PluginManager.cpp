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


////////////////////////////////////////////////////////////
// Headers
////////////////////////////////////////////////////////////
#include <Pluma/PluginManager.hpp>
#include <Pluma/DLibrary.hpp>
#include <Pluma/Dir.hpp>
#include <cstdio>

namespace pluma{

////////////////////////////////////////////////////////////
PluginManager::PluginManager(){
    // Nothing to do
}


////////////////////////////////////////////////////////////
PluginManager::~PluginManager(){
    unloadAll();
}


////////////////////////////////////////////////////////////
bool PluginManager::load(const std::string& path){
    std::string plugName = getPluginName(path);
    std::string realPath = resolvePathExtension(path);
    DLibrary* lib = DLibrary::load(realPath);
    if (!lib) return false;

    fnRegisterPlugin* registerFunction;
    registerFunction = reinterpret_cast<fnRegisterPlugin*>(lib->getSymbol("connect"));

    if(!registerFunction){
        fprintf(stderr, "Failed to initialize plugin \"%s\": connect function not found\n", plugName.c_str());
        delete lib;
        return false;
    }
    // try to initialize plugin:
    if (!registerFunction(host)){
        // plugin decided to fail
        fprintf(stderr, "Self registry failed on plugin \"%s\".\n", plugName.c_str());
        host.cancelAddictions();
        delete lib;
        return false;
    }
    // Store the library if addictions are confirmed
    if (host.confirmAddictions())
        libraries[plugName] = lib;
    else{
        // otherwise nothing was registered
        fprintf(stderr, "Nothing registered by plugin \"%s\".\n", plugName.c_str());
        delete lib;
        return false;
    }
    return true;
}


////////////////////////////////////////////////////////////
bool PluginManager::load(const std::string& folder, const std::string& pluginName){
    if (folder.empty())
        return load(pluginName);
    else if (folder[folder.size()-1] == '/' || folder[folder.size()-1] == '\\')
        return load(folder + pluginName);
    return load(folder + '/' + pluginName);
}


////////////////////////////////////////////////////////////
int PluginManager::loadFromFolder(const std::string& folder, bool recursive){
    std::list<std::string> files;
    dir::listFiles(files, folder, PLUMA_LIB_EXTENSION, recursive);
    // try to load every library
    int res = 0;
    std::list<std::string>::const_iterator it;
    for (it = files.begin() ; it != files.end() ; ++it){
        if ( load(*it) ) ++res;
    }
    return res;
}


////////////////////////////////////////////////////////////
bool PluginManager::unload(const std::string& pluginName){
    std::string plugName = getPluginName(pluginName);
    LibMap::iterator it = libraries.find(plugName);
    if( it != libraries.end() ) {
        delete it->second;
        libraries.erase(it);
        return true;
    }
    return false;
}


////////////////////////////////////////////////////////////
void PluginManager::unloadAll(){

    host.clearProviders();
    LibMap::iterator it;
    for (it = libraries.begin() ; it != libraries.end() ; ++it){
        delete it->second;
    }
    libraries.clear();
}


////////////////////////////////////////////////////////////
std::string PluginManager::getPluginName(const std::string& path){
    size_t lastDash = path.find_last_of("/\\");
    size_t lastDot = path.find_last_of('.');
    if (lastDash == std::string::npos) lastDash = 0;
    else ++lastDash;
    if (lastDot < lastDash || lastDot == std::string::npos){
        // path without extension
        lastDot = path.length();
    }
    return path.substr(lastDash, lastDot-lastDash);
}


////////////////////////////////////////////////////////////
std::string PluginManager::resolvePathExtension(const std::string& path){
    size_t lastDash = path.find_last_of("/\\");
    size_t lastDot = path.find_last_of('.');
    if (lastDash == std::string::npos) lastDash = 0;
    else ++lastDash;
    if (lastDot < lastDash || lastDot == std::string::npos){
        // path without extension, add it
        return path + "." + PLUMA_LIB_EXTENSION;
    }
    return path;
}


////////////////////////////////////////////////////////////
void PluginManager::registerType(const std::string& type, unsigned int version, unsigned int lowestVersion){
    host.registerType(type, version, lowestVersion);
}


////////////////////////////////////////////////////////////
bool PluginManager::addProvider(Provider* provider){
    if (provider == NULL){
        fprintf(stderr, "Trying to add null provider\n");
        return false;
    }
    return host.registerProvider(provider);
}


////////////////////////////////////////////////////////////
void PluginManager::getLoadedPlugins(std::vector<const std::string*>& pluginNames) const{
    pluginNames.reserve(pluginNames.size()+libraries.size());
    LibMap::const_iterator it;
    for(it = libraries.begin() ; it != libraries.end() ; ++it){
        pluginNames.push_back(&(it->first));
    }
}


////////////////////////////////////////////////////////////
bool PluginManager::isLoaded(const std::string& pluginName) const{
    return libraries.find(getPluginName(pluginName)) != libraries.end();
}


////////////////////////////////////////////////////////////
const std::list<Provider*>* PluginManager::getProviders(const std::string& type) const{
    return host.getProviders(type);
}



}   // namespace pluma

