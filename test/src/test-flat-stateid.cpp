#include "uscxml/transform/FlatStateIdentifier.h"
#include <cassert>

int main(int argc, char** argv) {
	std::list<std::string>::const_iterator listIter;

	{
		std::string stateId = "active:{}";
		uscxml::FlatStateIdentifier flat1(stateId);
		assert(flat1.getActive().size() == 0);
		assert(flat1.getVisited().size() == 0);
		assert(flat1.getHistory().size() == 0);
		
		uscxml::FlatStateIdentifier flat2(flat1.getActive(), flat1.getVisited(), flat1.getHistory());
		assert(flat2.getStateId() == stateId);
	}

	{
		std::string stateId = "active:{s1};entered:{s1,s2}";
		uscxml::FlatStateIdentifier flat1(stateId);
		assert(flat1.getActive().size() == 1);
		assert(flat1.getVisited().size() == 2);
		assert(flat1.getHistory().size() == 0);
		
		uscxml::FlatStateIdentifier flat2(flat1.getActive(), flat1.getVisited(), flat1.getHistory());
		assert(flat2.getStateId() == stateId);
	}

	{
		
		std::string stateId = "active:{s0,s1,s2};entered:{s0,s1,s2};history:{h0:{s1,s2},h1:{s2,s3}}";
		uscxml::FlatStateIdentifier flat1(stateId);
		
		listIter = flat1.getActive().begin();
		assert(*listIter++ == "s0");
		assert(*listIter++ == "s1");
		assert(*listIter++ == "s2");
		
		listIter = flat1.getVisited().begin();
		assert(*listIter++ == "s0");
		assert(*listIter++ == "s1");
		assert(*listIter++ == "s2");
		
		assert(flat1.getHistory().find("h0") != flat1.getHistory().end());
		listIter = flat1.getHistory().at("h0").begin();
		assert(*listIter++ == "s1");
		assert(*listIter++ == "s2");

		assert(flat1.getHistory().find("h1") != flat1.getHistory().end());
		listIter = flat1.getHistory().at("h1").begin();
		assert(*listIter++ == "s2");
		assert(*listIter++ == "s3");

		uscxml::FlatStateIdentifier flat2(flat1.getActive(), flat1.getVisited(), flat1.getHistory());
		assert(flat2.getStateId() == stateId);
	}
}