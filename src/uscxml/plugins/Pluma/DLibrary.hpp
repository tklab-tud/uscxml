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

#ifndef PLUMA_DYNAMIC_LIBRARY_HPP
#define PLUMA_DYNAMIC_LIBRARY_HPP

////////////////////////////////////////////////////////////
// Headers
////////////////////////////////////////////////////////////
#include <Pluma/Config.hpp>
#include <string>

// include OS dependent support for DLL
#ifdef PLUMA_SYS_WINDOWS
    #include <Windows.h>
#else
    #include <dlfcn.h>
#endif



namespace pluma{

////////////////////////////////////////////////////////////
/// \brief Manages a Dynamic Linking Library.
///
////////////////////////////////////////////////////////////
class DLibrary{


public:

    ////////////////////////////////////////////////////////////
    /// \brief Load a library.
    ///
    /// \param path Path to the library.
    ///
    /// \return Pointer to the loaded library, or NULL if failed.
    ///
    ////////////////////////////////////////////////////////////
    static DLibrary* load(const std::string& path);

    ////////////////////////////////////////////////////////////
    /// \brief Destructor.
    ///
    /// Close and free the opened library (if any).
    ///
    ////////////////////////////////////////////////////////////
    ~DLibrary();

    ////////////////////////////////////////////////////////////
    /// \brief Get a symbol from the library.
    ///
    /// \param symbol Symbol that we're looking for.
    ///
    /// \return Pointer to what the symbol refers to, or NULL if
    /// the symbol is not found.
    ///
    ////////////////////////////////////////////////////////////
    void* getSymbol(const std::string& symbol);


private:

    ////////////////////////////////////////////////////////////
    /// \brief Default constructor.
    ///
    /// Library instances cannot be created, use load instead.
    ///
    /// \see load
    ///
    ////////////////////////////////////////////////////////////
    DLibrary();

    ////////////////////////////////////////////////////////////
    /// \brief Constructor via library handle.
    ///
    /// Used on load function.
    ///
    /// \see load
    ///
    ////////////////////////////////////////////////////////////
    DLibrary(void* handle);



////////////////////////////////////////////////////////////
// Member data
////////////////////////////////////////////////////////////


private:

    void* handle; ///< Library handle.

};


}   // namespace pluma


#endif // PLUMA_DYNAMIC_LIBRARY_HPP
