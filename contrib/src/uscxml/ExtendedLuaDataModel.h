/**
 *  @file
 *  @author     2017 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#ifndef EXTENDEDLUADATAMODEL_H_9ED3DCC6
#define EXTENDEDLUADATAMODEL_H_9ED3DCC6

#include "uscxml/plugins/datamodel/lua/LuaDataModel.h"

class ExtendedLuaDataModel : public uscxml::LuaDataModel {
public:
    ExtendedLuaDataModel() {};
    
    std::shared_ptr<DataModelImpl> create(uscxml::DataModelCallbacks* callbacks) {
        
        std::shared_ptr<ExtendedLuaDataModel> dm(new ExtendedLuaDataModel());
//        dm->LuaDataModel::init(callbacks);
        
        lua_pushcfunction(dm->_luaState, GetSomeResult);
        lua_setglobal(dm->_luaState, "GetSomeResult");
        
        return dm;
    }
    
    static int GetSomeResult(lua_State * L) {
        LOGD(uscxml::USCXML_INFO) << "Calling GetSomeResult!" << std::endl;
        lua_pushinteger(L, 55555);
        return 1;
    }
};



#endif /* end of include guard: EXTENDEDLUADATAMODEL_H_9ED3DCC6 */
