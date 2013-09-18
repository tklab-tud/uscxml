#ifndef UUID_H_8X65R2EI
#define UUID_H_8X65R2EI

#include <boost/uuid/uuid.hpp>
#include <boost/uuid/uuid_generators.hpp>
#include <boost/uuid/uuid_io.hpp>
#include <ostream>

namespace uscxml {

class UUID {
public:
	static std::string getUUID();
	static boost::uuids::random_generator uuidGen;
};
	
}


#endif /* end of include guard: UUID_H_8X65R2EI */
