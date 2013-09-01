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