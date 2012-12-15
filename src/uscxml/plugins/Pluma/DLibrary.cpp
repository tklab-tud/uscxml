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
#include <Pluma/DLibrary.hpp>
#include <cstdio>
#include <string>


namespace pluma{

////////////////////////////////////////////////////////////
DLibrary* DLibrary::load(const std::string& path){
    if ( path.empty() ){
        fprintf(stderr, "Failed to load library: Empty path\n");
        return NULL;
    }
    void* handle = NULL;

    // load library - OS dependent operation
    #ifdef PLUMA_SYS_WINDOWS
        handle = ::LoadLibraryA(path.c_str());
        if (!handle){
            fprintf(stderr, "Failed to load library \"%s\".\n", path.c_str());
            return NULL;
        }
    #else
        handle = ::dlopen(path.c_str(), RTLD_NOW);
        if (!handle){
            const char* errorString = ::dlerror();
            fprintf(stderr, "Failed to load library \"%s\".", path.c_str());
            if(errorString) fprintf(stderr, " OS returned error: \"%s\".", errorString);
            fprintf(stderr, "\n");
            return NULL;
        }
    #endif
    // return a DLibrary with the DLL handle
    return new DLibrary(handle);
}


////////////////////////////////////////////////////////////
DLibrary::~DLibrary(){
    if (handle){
        #ifdef PLUMA_SYS_WINDOWS
            ::FreeLibrary( (HMODULE)handle );
        #else
            ::dlclose(handle);
        #endif
    }
}


////////////////////////////////////////////////////////////
void* DLibrary::getSymbol(const std::string& symbol){
    if (!handle){
        fprintf(stderr, "Cannot inspect library symbols, library isn't loaded.\n");
        return NULL;
    }
    void* res;
    #ifdef PLUMA_SYS_WINDOWS
        res = (void*)(::GetProcAddress((HMODULE)handle, symbol.c_str()));
    #else
        res = (void*)(::dlsym(handle, symbol.c_str()));
    #endif
    if (!res){
        fprintf(stderr, "Library symbol \"%s\" not found.\n", symbol.c_str());
        return NULL;
    }
    return res;
}


////////////////////////////////////////////////////////////
DLibrary::DLibrary(void* handle):
    handle(handle)
{
    // Nothing to do
}

}   // namespace pluma

