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
#include <Pluma/Host.hpp>
#include <cstdio>


namespace pluma{

////////////////////////////////////////////////////////////
Host::Host(){
    // Nothing to do
}


////////////////////////////////////////////////////////////
bool Host::add(Provider* provider){
    if (provider == NULL){
        fprintf(stderr, "Trying to add a null provider.\n");
        return false;
    }
    if (!validateProvider(provider)){
        delete provider;
        return false;
    }
    addRequests[ provider->plumaGetType() ].push_back(provider);
    return true;
}


////////////////////////////////////////////////////////////
Host::~Host(){
    clearProviders();
    // map frees itself
}


////////////////////////////////////////////////////////////
void Host::clearProviders(){
    ProvidersMap::iterator it;
    for (it = knownTypes.begin() ; it != knownTypes.end() ; ++it){
        std::list<Provider*>& providers = it->second.providers;
        std::list<Provider*>::iterator provIt;
        for (provIt = providers.begin() ; provIt != providers.end() ; ++provIt){
            delete *provIt;
        }
        std::list<Provider*>().swap(providers);
    }
}


////////////////////////////////////////////////////////////
bool Host::knows(const std::string& type) const{
    return knownTypes.find(type) != knownTypes.end();
}


////////////////////////////////////////////////////////////
unsigned int Host::getVersion(const std::string& type) const{
    ProvidersMap::const_iterator it = knownTypes.find(type);
    if (it != knownTypes.end())
        return it->second.version;
    return 0;
}


////////////////////////////////////////////////////////////
unsigned int Host::getLowestVersion(const std::string& type) const{
    ProvidersMap::const_iterator it = knownTypes.find(type);
    if (it != knownTypes.end())
        return it->second.lowestVersion;
    return 0;
}


////////////////////////////////////////////////////////////
void Host::registerType(const std::string& type, unsigned int version, unsigned int lowestVersion){
    if (!knows(type)){
        ProviderInfo pi;
        pi.version = version;
        pi.lowestVersion = lowestVersion;
        knownTypes[type] = pi;
    }
}


////////////////////////////////////////////////////////////
const std::list<Provider*>* Host::getProviders(const std::string& type) const{
    ProvidersMap::const_iterator it = knownTypes.find(type);
    if (it != knownTypes.end())
        return &it->second.providers;
    return NULL;
}


////////////////////////////////////////////////////////////
bool Host::validateProvider(Provider* provider) const{
    const std::string& type = provider->plumaGetType();
    if ( !knows(type) ){
        fprintf(stderr, "%s provider type isn't registered.\n", type.c_str());
        return false;
    }
    if (!provider->isCompatible(*this)){
        fprintf(stderr, "Incompatible %s provider version.\n", type.c_str());
        return false;
    }
    return true;
}


////////////////////////////////////////////////////////////
bool Host::registerProvider(Provider* provider){
    if (!validateProvider(provider)){
        delete provider;
        return false;
    }
    knownTypes[ provider->plumaGetType() ].providers.push_back(provider);
    return true;
}


////////////////////////////////////////////////////////////
void Host::cancelAddictions(){
    TempProvidersMap::iterator it;
    for( it = addRequests.begin() ; it != addRequests.end() ; ++it){
        std::list<Provider*> lst = it->second;
        std::list<Provider*>::iterator providerIt;
        for (providerIt = lst.begin() ; providerIt != lst.end() ; ++providerIt){
            delete *providerIt;
        }
    }
    // clear map
    TempProvidersMap().swap(addRequests);
}


////////////////////////////////////////////////////////////
bool Host::confirmAddictions(){
    if (addRequests.empty()) return false;
    TempProvidersMap::iterator it;
    for( it = addRequests.begin() ; it != addRequests.end() ; ++it){
        std::list<Provider*> lst = it->second;
        std::list<Provider*>::iterator providerIt;
        for (providerIt = lst.begin() ; providerIt != lst.end() ; ++providerIt){
            knownTypes[it->first].providers.push_back(*providerIt);
        }
    }
    // clear map
    TempProvidersMap().swap(addRequests);
    return true;
}


} //namespace pluma
