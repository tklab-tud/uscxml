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

#ifndef STORAGE_H_L672TNX
#define STORAGE_H_L672TNX

#include <string>
#include <map>

namespace uscxml {

class Storage {
public:
	Storage(const std::string& filename);
	~Storage();

	unsigned long getLength();
	std::string key(unsigned long index);
	std::string getItem(const std::string& key);
	void setItem(const std::string& key, const std::string& value);
	void removeItem(const std::string& key);
	void clear();

protected:
	std::map<std::string, std::string> _data;
	std::string _filename;
};

}

#endif /* end of include guard: STORAGE_H_L672TNX */
