/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "Storage.h"
#include <iostream>

namespace uscxml {

Storage::Storage(const std::string& filename) {
	_filename = filename;
//	std::cout << _filename << std::endl;
	std::fstream file;
	file.open(_filename.c_str(), std::ios_base::in);
	// read content into data
	std::string key;
	std::string value;

	while(std::getline(file, key, '\0')) {
		if(std::getline(file, value, '\0')) {
			_data[key] = value;
		}
	}
	file.close();
}

Storage::~Storage() {
	std::fstream file;
	file.open(_filename.c_str(), std::ios_base::out);
//		file.clear();

	std::map<std::string, std::string>::iterator dataIter = _data.begin();
	while(dataIter != _data.end()) {
		// include trailing \0
		file.write(dataIter->first.c_str(), dataIter->first.length() + 1);
		file.write(dataIter->second.c_str(), dataIter->second.length() + 1);
		dataIter++;
	}
//		file.flush();
	file.close();
}

unsigned long Storage::getLength() {
	return _data.size();
}

std::string Storage::key(unsigned long index) {
	if (index > getLength())
		return "";

	std::map<std::string, std::string>::iterator dataIter = _data.begin();
	for (unsigned int i = 0; i < index; i++) {
		dataIter++;
	}
	return dataIter->first;
}

std::string Storage::getItem(const std::string& key) {
	if (_data.find(key) == _data.end())
		return "";
	return _data[key];
}

void Storage::setItem(const std::string& key, const std::string& value) {
	_data[key] = value;
}

void Storage::removeItem(const std::string& key) {
	if (_data.find(key) == _data.end())
		return;
	_data.erase(key);
}

void Storage::clear() {
	_data.clear();
}

}