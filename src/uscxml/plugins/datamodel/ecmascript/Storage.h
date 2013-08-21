#ifndef STORAGE_H_L672TNX
#define STORAGE_H_L672TNX

#include <string>
#include <map>
#include <fstream>
#include <istream>

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
