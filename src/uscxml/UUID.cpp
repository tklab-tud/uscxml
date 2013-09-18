#include "UUID.h"
#include <sstream>

namespace uscxml {
boost::uuids::random_generator UUID::uuidGen;

std::string UUID::getUUID() {
	boost::uuids::uuid uuid = uuidGen();
	std::ostringstream os;
	os << uuid;
	return os.str();
}

}