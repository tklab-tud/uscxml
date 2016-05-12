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

#ifndef PLUMA_DIRECTORY_HPP
#define PLUMA_DIRECTORY_HPP

////////////////////////////////////////////////////////////
// Headers
////////////////////////////////////////////////////////////
#include <Pluma/Config.hpp>
#include <string>
#include <list>


namespace pluma{

namespace dir{

////////////////////////////////////////////////////////////
/// \brief List files of a directory.
///
/// \param list The output files list.
/// \param folder The folder where to search in
/// \param extension A file extension filter,
/// empty extension will match all files.
/// \param recursive If true it will list files in
/// sub directories as well.
///
////////////////////////////////////////////////////////////
void listFiles(
    std::list<std::string>& list,
    const std::string& folder,
    const std::string& extension = "",
    bool recursive = false
);


}   // namespace dir

}   // namespace pluma


#endif // PLUMA_DIRECTORY_HPP
