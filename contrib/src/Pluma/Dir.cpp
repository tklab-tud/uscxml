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
#include <Pluma/Dir.hpp>
#include <Pluma/uce-dirent.h>
#include <cstdio>
#include <queue>


namespace pluma{

namespace dir{


////////////////////////////////////////////////////////////
void listFiles(std::list<std::string>& list, const std::string& folder, const std::string& extension, bool recursive){
    DIR* dir;
    DIR* subDir;
    struct dirent *ent;
    // try to open top folder
    dir = opendir(folder.c_str());
    if (dir == NULL){
        // could not open directory
      fprintf(stderr, "Could not open \"%s\" directory.\n", folder.c_str());
      return;
    }else{
        // close, we'll process it next
        closedir(dir);
    }
    // enqueue top folder
    std::queue<std::string> folders;
    folders.push(folder);

    // run while has queued folders
    while (!folders.empty()){
        std::string currFolder = folders.front();
        folders.pop();
        dir = opendir(currFolder.c_str());
        if (dir == NULL) continue;
        // iterate through all the files and directories
        while ((ent = readdir (dir)) != NULL) {
            std::string name(ent->d_name);
            // ignore "." and ".." directories
            if ( name.compare(".") == 0 || name.compare("..") == 0) continue;
            // add path to the file name
            std::string path = currFolder;
            path.append("/");
            path.append(name);
            // check if it's a folder by trying to open it
            subDir = opendir(path.c_str());
            if (subDir != NULL){
                // it's a folder: close, we can process it later
                closedir(subDir);
                if (recursive) folders.push(path);
            }else{
                // it's a file
                if (extension.empty()){
                    list.push_back(path);
                }else{
                    // check file extension
                    size_t lastDot = name.find_last_of('.');
                    std::string ext = name.substr(lastDot+1);
                    if (ext.compare(extension) == 0){
                        // match
                        list.push_back(path);
                    }
                } // endif (extension test)
            } // endif (folder test)
        } // endwhile (nextFile)
        closedir(dir);
    } // endwhile (queued folders)

} // end listFiles


}   // namespace dir

}   // namespace pluma
