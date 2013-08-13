package org.uscxml;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class Data {
	public Map<String, Data> compound = new HashMap<String, Data>();
	public List<Data> array = new LinkedList<Data>();
	public String atom;
	public Type type = Type.INTERPRETED;

	public enum Type {
	    VERBATIM, INTERPRETED 
	}

	public static Data fromJSON(String jsonString) {
		return new Data(DataNative.fromJSON(jsonString));
	}
	
	public Data() {
	}
	
	public Data(String atom, Data.Type type) {
		this.atom = atom;
		this.type = type;
	}
	
	public Data(DataNative nativeData) {
		if (!nativeData.getCompound().empty()) {
			// data is a key value compound
			for(String key : nativeData.getCompound()) {
				this.compound.put(key, new Data(nativeData.getCompound().get(key)));
			}
		} else if (!nativeData.getArray().isEmpty()) {
			// data is an array
			for (int i = 0; i < nativeData.getArray().size(); i++) {
				this.array.add(new Data(nativeData.getArray().get(i)));
			}
		} else {
			// data is a single atom
			this.atom = nativeData.getAtom();
			if (nativeData.getType() == DataNative.Type.INTERPRETED) {
				this.type = Type.INTERPRETED;
			} else {
				this.type = Type.VERBATIM;				
			}
		}
	}
	
	@Override
	public String toString() {
		return toJSON();
	}

	public String toJSON() {
		DataNative nativeData = toNative(this);
		return DataNative.toJSON(nativeData);
	}

	public static DataNative toNative(Data data) {
		DataNative nativeData = new DataNative();
		//nativeData.swigCMemOwn = false;
		if (data.compound != null && !data.compound.isEmpty()) {
			DataMap nativeDataMap = new DataMap();
			for (String key : data.compound.keySet()) {
				nativeDataMap.set(key, toNative(data.compound.get(key)));
			}
			nativeData.setCompound(nativeDataMap);
		} else if (data.array != null && !data.array.isEmpty()) {
			DataList nativeDataList = new DataList();
			for (Data item : data.array) {
				nativeDataList.add(toNative(item));
			}
			nativeData.setArray(nativeDataList);
		} else {
			nativeData.setAtom(data.atom);
			if (data.type == Type.INTERPRETED) {
				nativeData.setType(DataNative.Type.INTERPRETED);
			} else {
				nativeData.setType(DataNative.Type.VERBATIM);				
			}
		}
		return nativeData;
	}

}
