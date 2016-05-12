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
inline Pluma::Pluma(){
    // Nothing to do
}


////////////////////////////////////////////////////////////
template<typename ProviderType>
void Pluma::acceptProviderType(){
    PluginManager::registerType(
        ProviderType::PLUMA_PROVIDER_TYPE,
        ProviderType::PLUMA_INTERFACE_VERSION,
        ProviderType::PLUMA_INTERFACE_LOWEST_VERSION
    );
}


////////////////////////////////////////////////////////////
template<typename ProviderType>
void Pluma::getProviders(std::vector<ProviderType*>& providers){
    const std::list<Provider*>* lst = PluginManager::getProviders(ProviderType::PLUMA_PROVIDER_TYPE);
    if (!lst) return;
    providers.reserve(providers.size() + lst->size());
    std::list<Provider*>::const_iterator it;
    for (it = lst->begin() ; it != lst->end() ; ++it)
        providers.push_back(static_cast<ProviderType*>(*it));
}
