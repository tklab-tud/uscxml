/**
 *  @file
 *  @author     2015-2016 Jens Heuschkel (heuschkel@tk.tu-darmstadt.de)
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

#ifndef CHARTOVHDL_H
#define CHARTOVHDL_H

#include "uscxml/interpreter/InterpreterDraft6.h"
#include "uscxml/dom/DOMUtils.h"
#include "uscxml/util/Trie.h"
#include "Transformer.h"
#include "ChartToC.h"

#include <DOM/Document.hpp>
#include <DOM/Node.hpp>
#include <XPath/XPath.hpp>
#include <ostream>
#include <vector>

namespace uscxml {

class USCXML_API ChartToVHDL : public ChartToC {
public:

	virtual ~ChartToVHDL();
	static Transformer transform(const Interpreter& other);

	void writeTo(std::ostream& stream);


	struct VNode {
		virtual void print(std::ostream& stream, const std::string padding = "") = 0;
		virtual ~VNode() {};
	};
	struct VBranch : VNode {
		std::vector< VNode* > v;
		virtual ~VBranch() {
			for(unsigned i = 0; i < v.size(); i++)
				delete v[i];
		}

		VBranch& operator +=(VNode* p ) {
			v.push_back(p);
			return *this;
		}
	};

	struct VPointer {
		VNode* ptr;

		operator VNode*() {
			return ptr;
		}

		VPointer& operator /( VNode* p ) {
			ptr = p;
			return *this;
		}
	};

	struct VContainer {
		VBranch* ptr;

		operator VBranch*() {
			return ptr;
		}
		VContainer& operator /( VBranch* p ) {
			ptr = p;
			return *this;
		}
		VContainer& operator , ( VPointer p ) {
			if(ptr) ptr->v.push_back(p.ptr);
			return *this;
		}
		VContainer& operator , ( VContainer c ) {
			if(ptr) ptr->v.push_back(c.ptr);
			return *this;
		}
	};

	struct VLine : VNode {
		VLine(const std::string& name) : name(name) {}
		virtual void print(std::ostream& stream, const std::string padding = "") {
			stream << " " << name;
		}

		std::string name;
	};

	struct VAssign : VBranch {
		virtual void print(std::ostream& stream, const std::string padding = "") {
			v[0]->print(stream, padding);
			stream << padding << " <=";
			v[1]->print(stream, padding + "  ");
		}
	};

	struct VAnd : VBranch {
		virtual void print(std::ostream& stream, const std::string padding = "") {
			stream << std::endl << padding << "( '1' ";
			for(unsigned i = 0; i < v.size(); i++) {
				stream << std::endl << padding << "  and";
				v[i]->print(stream, padding + "    ");
			}
			stream << padding << ")" << std::endl;
		}
	};

	struct VOr : VBranch {
		virtual void print(std::ostream& stream, const std::string padding = "") {
			stream << std::endl << padding << "( '0' ";
			for(unsigned i = 0; i < v.size(); i++) {
				stream << std::endl << padding << "  or";
				v[i]->print(stream, padding + "    ");
			}
			stream << std::endl << padding << ")" << std::endl;
		}
	};

	struct VNot : VBranch {
		virtual void print(std::ostream& stream, const std::string padding = "") {
			stream << " ( not";
			v[0]->print(stream, padding + "  ");
			stream << " )";
		}
	};

	struct VNop : VBranch {
		virtual void print(std::ostream& stream, const std::string padding = "") {
			v[0]->print(stream, padding);
		}
	};


#define VLINE   VPointer()/new VLine
#define VASSIGN VContainer()/new VAssign
#define VOR     VContainer()/new VOr
#define VAND    VContainer()/new VAnd
#define VNOT    VContainer()/new VNot
#define VNOP    VContainer()/new VNop



protected:
	ChartToVHDL(const Interpreter& other);

	void checkDocument();
	void findEvents();

	void writeIncludes(std::ostream& stream);
	void writeTopDown(std::ostream& stream);

	void writeTypes(std::ostream& stream);

	void writeOptimalTransitionSetSelection(std::ostream& stream);
	void writeExitSet(std::ostream & stream);
	void writeEntrySet(std::ostream & stream);

	void writeNextStateLogic(std::ostream& stream);
	void writeOutputLogic(std::ostream& stream);
	void writeSignals(std::ostream& stream);
	void writeFiFo(std::ostream& stream);
	void writeModuleInstantiation(std::ostream& stream);
	void writeErrorHandler(std::ostream& stream);
	void writeFSM(std::ostream& stream);

	void writeTransitionSet(std::ostream & stream);

	Trie _eventTrie;

private:
	std::string eventNameEscape(const std::string& eventName);


};

}

#endif /* end of include guard: FSMTOCPP_H_201672B0 */
