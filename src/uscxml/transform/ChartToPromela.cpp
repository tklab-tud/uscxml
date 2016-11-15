/**
 *  @file
 *  @author   2012-2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "uscxml/transform/ChartToPromela.h"
#include "uscxml/util/Predicates.h"
#include "uscxml/util/String.h"
#include "uscxml/plugins/datamodel/promela/PromelaParser.h"
#include "uscxml/plugins/datamodel/promela/parser/promela.tab.hpp"

#include <boost/algorithm/string.hpp>
#include <easylogging++.h>

#include <algorithm>

#define ADAPT_SRC(code) _analyzer.adaptCode(code, _prefix)
#define BIT_WIDTH(number) (number > 1 ? (int)ceil(log((double)number) / log((double)2.0)) : 1)
#define EVENT_NAME (_analyzer.usesComplexEventStruct() ? "_event.name" : "_event")

namespace uscxml {

using namespace XERCESC_NS;


Transformer ChartToPromela::transform(const Interpreter& other) {
	return std::shared_ptr<TransformerImpl>(new ChartToPromela(other));
}

ChartToPromela::~ChartToPromela() {
}

/**
 The following tests FAILED:
 1740 - w3c/spin/promela/test150.scxml (Failed)
 1741 - w3c/spin/promela/test151.scxml (Failed)
 1742 - w3c/spin/promela/test152.scxml (Failed)
 1743 - w3c/spin/promela/test153.scxml (Failed)
 1744 - w3c/spin/promela/test155.scxml (Failed)
 1745 - w3c/spin/promela/test156.scxml (Failed)
 1749 - w3c/spin/promela/test173.scxml (Failed)
 1750 - w3c/spin/promela/test174.scxml (Failed)
 1752 - w3c/spin/promela/test176.scxml (Failed)
 1753 - w3c/spin/promela/test178.scxml (Failed)
 1754 - w3c/spin/promela/test179.scxml (Failed)
 1757 - w3c/spin/promela/test186.scxml (Failed)
 1762 - w3c/spin/promela/test192.scxml (Failed)
 1763 - w3c/spin/promela/test193.scxml (Failed)
 1765 - w3c/spin/promela/test198.scxml (Failed)
 1769 - w3c/spin/promela/test205.scxml (Failed)
 1770 - w3c/spin/promela/test207.scxml (Failed)
 1771 - w3c/spin/promela/test208.scxml (Failed)
 1772 - w3c/spin/promela/test210.scxml (Failed)
 1773 - w3c/spin/promela/test215.scxml (Failed)
 1774 - w3c/spin/promela/test216.scxml (Failed)
 1776 - w3c/spin/promela/test223.scxml (Failed)
 1777 - w3c/spin/promela/test224.scxml (Failed)
 1778 - w3c/spin/promela/test225.scxml (Failed)
 1780 - w3c/spin/promela/test228.scxml (Failed)
 1782 - w3c/spin/promela/test230.scxml (Failed)
 1783 - w3c/spin/promela/test232.scxml (Failed)
 1785 - w3c/spin/promela/test234.scxml (Failed)
 1787 - w3c/spin/promela/test236.scxml (Failed)
 1788 - w3c/spin/promela/test237.scxml (Failed)
 1789 - w3c/spin/promela/test239.scxml (Failed)
 1790 - w3c/spin/promela/test240.scxml (Failed)
 1791 - w3c/spin/promela/test241.scxml (Failed)
 1792 - w3c/spin/promela/test242.scxml (Failed)
 1797 - w3c/spin/promela/test250.scxml (Failed)
 1798 - w3c/spin/promela/test252.scxml (Failed)
 1799 - w3c/spin/promela/test253.scxml (Failed)
 1802 - w3c/spin/promela/test278.scxml (Failed)
 1803 - w3c/spin/promela/test279.scxml (Failed)
 1805 - w3c/spin/promela/test286.scxml (Failed)
 1808 - w3c/spin/promela/test294.scxml (Failed)
 1809 - w3c/spin/promela/test298.scxml (Failed)
 1811 - w3c/spin/promela/test302.scxml (Failed)
 1813 - w3c/spin/promela/test304.scxml (Failed)
 1814 - w3c/spin/promela/test309.scxml (Failed)
 1815 - w3c/spin/promela/test310.scxml (Failed)
 1816 - w3c/spin/promela/test311.scxml (Failed)
 1817 - w3c/spin/promela/test312.scxml (Failed)
 1818 - w3c/spin/promela/test313.scxml (Failed)
 1819 - w3c/spin/promela/test314.scxml (Failed)
 1820 - w3c/spin/promela/test318.scxml (Failed)
 1823 - w3c/spin/promela/test322.scxml (Failed)
 1825 - w3c/spin/promela/test324.scxml (Failed)
 1827 - w3c/spin/promela/test326.scxml (Failed)
 1828 - w3c/spin/promela/test329.scxml (Failed)
 1829 - w3c/spin/promela/test330.scxml (Failed)
 1830 - w3c/spin/promela/test331.scxml (Failed)
 1831 - w3c/spin/promela/test332.scxml (Failed)
 1832 - w3c/spin/promela/test333.scxml (Failed)
 1833 - w3c/spin/promela/test335.scxml (Failed)
 1835 - w3c/spin/promela/test337.scxml (Failed)
 1837 - w3c/spin/promela/test339.scxml (Failed)
 1838 - w3c/spin/promela/test342.scxml (Failed)
 1839 - w3c/spin/promela/test343.scxml (Failed)
 1840 - w3c/spin/promela/test344.scxml (Failed)
 1841 - w3c/spin/promela/test346.scxml (Failed)
 1842 - w3c/spin/promela/test347.scxml (Failed)
 1846 - w3c/spin/promela/test351.scxml (Failed)
 1847 - w3c/spin/promela/test352.scxml (Failed)
 1848 - w3c/spin/promela/test354.scxml (Failed)
 1849 - w3c/spin/promela/test355.scxml (Failed)
 1850 - w3c/spin/promela/test364.scxml (Failed)
 1851 - w3c/spin/promela/test372.scxml (Failed)
 1854 - w3c/spin/promela/test377.scxml (Failed)
 1855 - w3c/spin/promela/test378.scxml (Failed)
 1856 - w3c/spin/promela/test387.scxml (Failed)
 1857 - w3c/spin/promela/test388.scxml (Failed)
 1858 - w3c/spin/promela/test396.scxml (Failed)
 1859 - w3c/spin/promela/test399.scxml (Failed)
 1860 - w3c/spin/promela/test401.scxml (Failed)
 1861 - w3c/spin/promela/test402.scxml (Failed)
 1862 - w3c/spin/promela/test403a.scxml (Failed)
 1863 - w3c/spin/promela/test403b.scxml (Failed)
 1864 - w3c/spin/promela/test403c.scxml (Failed)
 1865 - w3c/spin/promela/test404.scxml (Failed)
 1866 - w3c/spin/promela/test405.scxml (Failed)
 1867 - w3c/spin/promela/test406.scxml (Failed)
 1868 - w3c/spin/promela/test407.scxml (Failed)
 1869 - w3c/spin/promela/test409.scxml (Failed)
 1870 - w3c/spin/promela/test411.scxml (Failed)
 1871 - w3c/spin/promela/test412.scxml (Failed)
 1872 - w3c/spin/promela/test413.scxml (Failed)
 1873 - w3c/spin/promela/test415.scxml (Failed)
 1874 - w3c/spin/promela/test416.scxml (Failed)
 1875 - w3c/spin/promela/test417.scxml (Failed)
 1877 - w3c/spin/promela/test421.scxml (Failed)
 1878 - w3c/spin/promela/test422.scxml (Failed)
 1880 - w3c/spin/promela/test487.scxml (Failed)
 1881 - w3c/spin/promela/test488.scxml (Failed)
 1882 - w3c/spin/promela/test495.scxml (Failed)
 1886 - w3c/spin/promela/test503.scxml (Failed)
 1887 - w3c/spin/promela/test504.scxml (Failed)
 1888 - w3c/spin/promela/test505.scxml (Failed)
 1890 - w3c/spin/promela/test509.scxml (Failed)
 1892 - w3c/spin/promela/test518.scxml (Failed)
 1893 - w3c/spin/promela/test519.scxml (Failed)
 1894 - w3c/spin/promela/test520.scxml (Failed)
 1897 - w3c/spin/promela/test525.scxml (Failed)
 1898 - w3c/spin/promela/test527.scxml (Failed)
 1899 - w3c/spin/promela/test528.scxml (Failed)
 1900 - w3c/spin/promela/test529.scxml (Failed)
 1901 - w3c/spin/promela/test530.scxml (Failed)
 1902 - w3c/spin/promela/test531.scxml (Failed)
 1903 - w3c/spin/promela/test532.scxml (Failed)
 1904 - w3c/spin/promela/test533.scxml (Failed)
 1905 - w3c/spin/promela/test534.scxml (Failed)
 1906 - w3c/spin/promela/test550.scxml (Failed)
 1907 - w3c/spin/promela/test551.scxml (Failed)
 1911 - w3c/spin/promela/test567.scxml (Failed)
 1912 - w3c/spin/promela/test570.scxml (Failed)
 1913 - w3c/spin/promela/test576.scxml (Failed)
 1915 - w3c/spin/promela/test579.scxml (Failed)
 1916 - w3c/spin/promela/test580.scxml (Failed)
*/

void ChartToPromela::prepare() {
    if (_machinesAll == NULL) {
        _machinesAll = new std::map<DOMNode*, ChartToPromela*>();
        (*_machinesAll)[_scxml] = this;
    }

    if (_machinesAllPerId == NULL)
        _machinesAllPerId = new std::map<std::string, XERCESC_NS::DOMNode* >();

    if (_parentTopMost == NULL)
        _parentTopMost = this;

    // transform data / assign json into PROMELA statements
    std::list<DOMElement*> values;
    
    values.splice(values.end(), DOMUtils::inDocumentOrder({XML_PREFIX(_scxml).str() + "assign"}, _scxml));
    values.splice(values.end(), DOMUtils::inDocumentOrder({XML_PREFIX(_scxml).str() + "data"}, _scxml));

    for (auto element : values) {
        std::string key;
        if (HAS_ATTR(element, "id")) {
            key = ATTR(element, "id");
        } else if (HAS_ATTR(element, "location")) {
            key = ATTR(element, "location");
        }
        
        if (key.length() == 0)
            continue;
        
        std::string value;
        if (HAS_ATTR(element, "expr")) {
            value = ATTR(element, "expr");
        } else if (HAS_ATTR(element, "src")) {
            URL absUrl = URL::resolve(ATTR_CAST(element, "src"), _baseURL);
            value = absUrl.getInContent();
        } else {
            std::list<DOMNode*> assignTexts = DOMUtils::filterChildType(DOMNode::TEXT_NODE, element, true);
            if (assignTexts.size() > 0) {
                for (auto assignText : assignTexts) {
                    value += X(assignText->getNodeValue()).str();
                }
            }
        }
        
        boost::trim(value);
        if (value.size() == 0)
            continue;
        
        // remove all children, we will replae by suitable promela statements
        while(element->hasChildNodes())
            element->removeChild(element->getFirstChild());

        std::string newValue;
        Data json = Data::fromJSON(value);
        if (!json.empty()) {
            newValue = dataToAssignments(key, json);
        } else {
            newValue = key + " = " + value + ";";
        }
        
        if (LOCALNAME(element) == "data")
            _varInitializers.push_back(newValue);

        DOMText* newText = _document->createTextNode(X(newValue));
        element->insertBefore(newText, NULL);

        _analyzer.addCode(newValue, this);

    }
}
    
void ChartToPromela::writeTo(std::ostream& stream) {

    _analyzer.analyze(this);
	// same preparations as the C transformation
    prepare();

	stream << "/** generated from " << std::endl;
	stream << "  " << std::string(_baseURL) << std::endl;
	stream << "  Use as:" << std::endl;
	stream << "  $ spin -a this.pml" << std::endl;
	stream << "  $ gcc pan.c -o pan" << std::endl;
	stream << "  $ ./pan -a -n -N w3c" << std::endl;
	stream << " */" << std::endl;
	stream << std::endl;


	writeMacros(stream);
	stream << std::endl;
    writeTypeDefs(stream);
    stream << std::endl;
    writeTypes(stream);
    stream << std::endl;
    writeStrings(stream);
    stream << std::endl;
    writeCancelEvents(stream);
    stream << std::endl;
	writeFSM(stream);
	stream << std::endl;


	stream << "init {" << std::endl;
    
    stream << "/* initialize state and transition information */" << std::endl;
	writeTransitions(stream);
	stream << std::endl;
	writeStates(stream);
    stream << std::endl;

    stream << "/* initialize data model variables */" << std::endl;
	stream << "  " << _prefix << "flags[USCXML_CTX_PRISTINE]  = true;" << std::endl;
	stream << "  " << _prefix << "flags[USCXML_CTX_SPONTANEOUS] = true;" << std::endl;

    for (auto initializer : _varInitializers) {
        stream << ADAPT_SRC(beautifyIndentation(initializer, 1)) << std::endl;
    }

    stream << std::endl;

	stream << "  run " << _prefix << "step() priority 10;" << std::endl;
	stream << "}" << std::endl;
	stream << std::endl;
	stream << "ltl w3c { eventually (" << _prefix << "config[" << _prefix << "PASS]) }" << std::endl;

}

void ChartToPromela::bit_clear_all(std::ostream& stream,
                                   const std::string& identifier,
                                   size_t length,
                                   size_t indent) {
	std::string padding;
	while (indent--)
		padding += "  ";
	stream << std::endl;
	stream << padding << "/** clearing all bits of " << identifier << " */" << std::endl;
	for (size_t i = 0; i < length; i++) {
		stream << padding << identifier << "[" << i << "] = false;" << std::endl;
	}
}

void ChartToPromela::bit_copy(std::ostream& stream,
                              const std::string& from,
                              const std::string& to,
                              size_t length,
                              size_t indent) {
	std::string padding;
	while (indent--)
		padding += "  ";
	stream << std::endl;
	stream << padding << "/** copy bits from " << from << " to " << to << " */" << std::endl;
	for (size_t i = 0; i < length; i++) {
		stream << padding << to << "[" << i << "] = "<< from << "[" << i << "];" << std::endl;
	}
}

void ChartToPromela::bit_or(std::ostream& stream,
                            const std::string& to,
                            const std::string& mask,
                            size_t length,
                            size_t indent) {
	std::string padding;
	while (indent--)
		padding += "  ";
	stream << std::endl;
	stream << padding << "/** or'ing bits in " << to << " with mask " << mask << " */" << std::endl;
	for (size_t i = 0; i < length; i++) {
		stream << padding << to << "[" << i << "] = "<< to << "[" << i << "] | " << mask << "[" << i << "];" << std::endl;
	}
}

void ChartToPromela::bit_and(std::ostream& stream,
                             const std::string& to,
                             const std::string& mask,
                             size_t length,
                             size_t indent) {
	std::string padding;
	while (indent--)
		padding += "  ";
	stream << std::endl;
	stream << padding << "/** and'ing bits in " << to << " with mask " << mask << " */" << std::endl;
	for (size_t i = 0; i < length; i++) {
		stream << padding << to << "[" << i << "] = "<< to << "[" << i << "] & " << mask << "[" << i << "];" << std::endl;
	}
}

void ChartToPromela::bit_and_not(std::ostream& stream,
                                 const std::string& to,
                                 const std::string& mask,
                                 size_t length,
                                 size_t indent) {
	std::string padding;
	while (indent--)
		padding += "  ";
	stream << std::endl;
	stream << padding << "/** not and'ing bits in " << to << " with mask " << mask << " */" << std::endl;
	for (size_t i = 0; i < length; i++) {
		stream << padding << to << "[" << i << "] = "<< to << "[" << i << "] & !" << mask << "[" << i << "];" << std::endl;
	}
}

void ChartToPromela::bit_has_and(std::ostream& stream,
                                 const std::string& a,
                                 const std::string& b,
                                 size_t length,
                                 size_t indent) {
	std::string padding;
	while (indent--)
		padding += "  ";
	stream << "(false /** is there a common bit in " << a << " and " << b << " */" << std::endl;
	for (size_t i = 0; i < length; i++) {
		stream << padding << " || " << a << "[" << i << "] & "<< b << "[" << i << "]" << std::endl;
	}
	stream << padding << ")";

}

void ChartToPromela::printBitArray(std::ostream& stream,
                                   const std::string& array,
                                   size_t length,
                                   size_t indent) {
	std::string padding;
	while (indent--)
		padding += "  ";

	stream << padding << "printf(\"";
	for (size_t i = 0; i < length; i++) {
		stream << "%d";
	}
	stream << "\", " << std::endl;
	for (size_t i = 0; i < length; i++) {
		stream << padding << "    " << array << "[" << toStr(i) << "]";
		if (i + 1 < length) {
			stream << ", " << std::endl;
		}
	}
	stream << ");" << std::endl;
}

void ChartToPromela::writeMacros(std::ostream& stream) {
	stream << "/* machine state flags */" << std::endl;
	stream << "#define USCXML_CTX_PRISTINE       0" << std::endl;
	stream << "#define USCXML_CTX_SPONTANEOUS    1" << std::endl;
	stream << "#define USCXML_CTX_INITIALIZED    2" << std::endl;
	stream << "#define USCXML_CTX_TOP_LEVEL_FINAL  3" << std::endl;
	stream << "#define USCXML_CTX_TRANSITION_FOUND   4" << std::endl;
	stream << "#define USCXML_CTX_FINISHED       5" << std::endl;
	stream << std::endl;

	stream << "#define USCXML_TRANS_SPONTANEOUS    0" << std::endl;
	stream << "#define USCXML_TRANS_TARGETLESS     1" << std::endl;
	stream << "#define USCXML_TRANS_INTERNAL     2" << std::endl;
	stream << "#define USCXML_TRANS_HISTORY      3" << std::endl;
	stream << "#define USCXML_TRANS_INITIAL      4" << std::endl;
	stream << std::endl;

	stream << "#define USCXML_STATE_ATOMIC       0" << std::endl;
	stream << "#define USCXML_STATE_PARALLEL     1" << std::endl;
	stream << "#define USCXML_STATE_COMPOUND     2" << std::endl;
	stream << "#define USCXML_STATE_FINAL      3" << std::endl;
	stream << "#define USCXML_STATE_HISTORY_DEEP   4" << std::endl;
	stream << "#define USCXML_STATE_HISTORY_SHALLOW  5" << std::endl;
	stream << "#define USCXML_STATE_INITIAL      6" << std::endl;
	stream << "#define USCXML_STATE_HAS_HISTORY    7" << std::endl;
	stream << std::endl;

	stream << "#define USCXML_ERR_OK         0" << std::endl;
	stream << "#define USCXML_ERR_DONE         1" << std::endl;
	stream << std::endl;

	stream << "#define USCXML_EVENT_SPONTANEOUS    0" << std::endl;
	stream << std::endl;
	stream << "#define TRACE_EXECUTION    1" << std::endl;
	stream << std::endl;


}

void ChartToPromela::writeTypeDefs(std::ostream& stream) {
    stream << "/* type definitions */" << std::endl;
    PromelaCodeAnalyzer::PromelaTypedef typeDefs = _analyzer.getTypes();
    if (typeDefs.types.size() == 0)
        return;
    
    std::list<PromelaCodeAnalyzer::PromelaTypedef> individualDefs;
    std::list<PromelaCodeAnalyzer::PromelaTypedef> currDefs;
    currDefs.push_back(typeDefs);
    
    while(currDefs.size() > 0) {
        if (std::find(individualDefs.begin(), individualDefs.end(), currDefs.front()) == individualDefs.end()) {
            individualDefs.push_back(currDefs.front());
            for (std::map<std::string, PromelaCodeAnalyzer::PromelaTypedef>::iterator typeIter = currDefs.front().types.begin(); typeIter != currDefs.front().types.end(); typeIter++) {
                currDefs.push_back(typeIter->second);
            }
        }
        currDefs.pop_front();
    }
    individualDefs.pop_front();
    
    for (std::list<PromelaCodeAnalyzer::PromelaTypedef>::reverse_iterator rIter = individualDefs.rbegin(); rIter != individualDefs.rend(); rIter++) {
        PromelaCodeAnalyzer::PromelaTypedef currDef = *rIter;
        
        if (currDef.types.size() == 0 || currDef.name.size() == 0)
            continue;
        
        stream << "typedef " << currDef.name << " {" << std::endl;
        if (currDef.name.compare("_event_t") ==0) {
            if (_analyzer.usesEventField("delay")) {
                // make sure delay is the first member for sorted enqueuing to work
                stream << "  int delay;" << std::endl;
#if NEW_DELAY_RESHUFFLE
#else
                stream << "  int seqNr;" << std::endl;
#endif
            }
            stream << "  int name;" << std::endl;
            if (_analyzer.usesEventField("invokeid")) {
                stream << "  int invokeid;" << std::endl;
            }
        }
        for (std::map<std::string, PromelaCodeAnalyzer::PromelaTypedef>::iterator tIter = currDef.types.begin(); tIter != currDef.types.end(); tIter++) {
            if (currDef.name.compare("_event_t") == 0 && (tIter->first.compare("name") == 0 ||
                                                          tIter->first.compare("seqNr") == 0 ||
                                                          tIter->first.compare("invokeid") == 0 ||
                                                          tIter->first.compare("delay") == 0)) { // special treatment for _event
                continue;
            }
            if (tIter->second.types.size() == 0) {
                stream << "  " << declForRange(tIter->first, tIter->second.minValue, tIter->second.maxValue, true) << ";" << std::endl; // not further nested
                //				stream << "  int " << tIter->first << ";" << std::endl; // not further nested
            } else {
                stream << "  " << tIter->second.name << " " << tIter->first << ";" << std::endl;
            }
        }
        stream << "};" << std::endl << std::endl;
    }
    
    //	stream << "/* typedef instances */" << std::endl;
    //	PromelaCodeAnalyzer::PromelaTypedef allTypes = _analyzer->getTypes();
    //	std::map<std::string, PromelaCodeAnalyzer::PromelaTypedef>::iterator typeIter = allTypes.types.begin();
    //	while(typeIter != allTypes.types.end()) {
    //		if (typeIter->second.types.size() > 0) {
    //			// an actual typedef
    //			stream << "hidden " << typeIter->second.name << " " << typeIter->first << ";" << std::endl;
    //		} else {
    //			stream << "hidden " << declForRange(typeIter->first, typeIter->second.minValue, typeIter->second.maxValue) << ";" << std::endl;
    //		}
    //		typeIter++;
    //	}
    
}


void ChartToPromela::writeTypes(std::ostream& stream) {
	stream << "/* type definitions and global variables */" << std::endl;
	stream << "bool " << _prefix << "flags[6];" << std::endl;
	stream << "bool " << _prefix << "config[" << _states.size() << "];" << std::endl;
	stream << "bool " << _prefix << "history[" << _states.size() << "];" << std::endl;
	stream << "bool " << _prefix << "invocations[" << _states.size() << "];" << std::endl;
	stream << "bool " << _prefix << "initialized_data[" << _states.size() << "];" << std::endl;
	
    size_t tolerance = 6;

    if (_analyzer.usesComplexEventStruct()) {
        // event is defined with the typedefs
        stream << "_event_t " << _prefix << "_event;               /* current event */" << std::endl;
        stream << "chan " << _prefix << "iQ   = [" << (std::max)(_internalQueueLength, (size_t)1) << "] of {_event_t}  /* internal queue */" << std::endl;
        stream << "chan " << _prefix << "eQ   = [" << _externalQueueLength + tolerance << "] of {_event_t}  /* external queue */" << std::endl;
        if (_allowEventInterleaving)
            stream << "chan " << _prefix << "tmpQ = [" << (std::max)(_externalQueueLength + tolerance, (size_t)1) << "] of {_event_t}  /* temporary queue for external events in transitions */" << std::endl;
    } else {
        stream << "unsigned " << _prefix << "_event : " << BIT_WIDTH(_analyzer.getLiterals().size() + 1) << ";                /* current event */" << std::endl;
        stream << "chan " << _prefix << "iQ   = [" << (std::max)(_internalQueueLength, (size_t)1) << "] of {int}  /* internal queue */" << std::endl;
        stream << "chan " << _prefix << "eQ   = [" << _externalQueueLength + tolerance << "] of {int}  /* external queue */" << std::endl;
        if (_allowEventInterleaving)
            stream << "chan " << _prefix << "tmpQ = [" << (std::max)(_externalQueueLength + tolerance, (size_t)1) << "] of {int}  /* temporary queue for external events in transitions */" << std::endl;
    }

	stream << std::endl;
	stream << "typedef transition {" << std::endl;
	stream << "  unsigned source : " << BIT_WIDTH(_states.size()) << ";" << std::endl;
	stream << "  bool target[" << _states.size() << "];" << std::endl;
	stream << "  bool type[5];" << std::endl;
	stream << "  bool conflicts[" << _transitions.size() << "];" << std::endl;
	stream << "  bool exit_set[" << _states.size() << "];" << std::endl;
	stream << "}" << std::endl;
	if (_transitions.size() > 0) {
		stream << "hidden transition " << _prefix << "transitions[" << toStr(_transitions.size()) << "];" << std::endl;
	}
	stream << std::endl;

	stream << "typedef state {" << std::endl;
	stream << "  unsigned parent : " << BIT_WIDTH(_states.size()) << ";" << std::endl;
	stream << "  bool children[" << _states.size() << "];" << std::endl;
	stream << "  bool completion[" << _states.size() << "];" << std::endl;
	stream << "  bool ancestors[" << _states.size() << "];" << std::endl;
	stream << "  bool type[8];" << std::endl;
	stream << "}" << std::endl;
	if (_states.size() > 0) {
		stream << "hidden state " << _prefix << "states[" << toStr(_states.size()) << "];" << std::endl;
	}
	stream << std::endl;

    stream << "hidden int tmpIndex;" << std::endl;
    if (_analyzer.usesComplexEventStruct()) {
        stream << "hidden _event_t tmpE;" << std::endl;
    } else {
        stream << "hidden int tmpE;" << std::endl;
    }

    if (_analyzer.hasIndexLessLoops())
        stream << "hidden int " << _prefix << "_index;             /* helper for indexless foreach loops */" << std::endl;

    if (_analyzer.usesEventField("sendid"))
        stream << "hidden int _lastSendId = 0;         /* sequential counter for send ids */" << std::endl;
    
    if (_analyzer.usesEventField("delay"))
        stream << "hidden int _lastSeqId = 0;     /* sequential counter for delayed events */"  << std::endl;

    stream << std::endl;

	std::set<std::string> processedIdentifiers;

	// automatic types
	std::list<DOMElement*> datas = DOMUtils::inDocumentOrder({ XML_PREFIX(_scxml).str() + "data" }, _scxml, false);
	PromelaCodeAnalyzer::PromelaTypedef allTypes = _analyzer.getTypes();

	for (auto data : datas) {
		std::string identifier = (HAS_ATTR_CAST(data, "id") ? ATTR_CAST(data, "id") : "");
		std::string type = boost::trim_copy(HAS_ATTR_CAST(data, "type") ? ATTR_CAST(data, "type") : "");

		_dataModelVars.insert(identifier);
		if (processedIdentifiers.find(identifier) != processedIdentifiers.end())
			continue;

		processedIdentifiers.insert(identifier);

		if (boost::starts_with(type, "string")) {
			type = "int" + type.substr(6, type.length() - 6);
		}

		if (type.length() == 0 || type == "auto") {
			if (allTypes.types.find(identifier) != allTypes.types.end()) {
				type = allTypes.types[identifier].name;
			} else {
				LOG(ERROR) << "Automatic or no type for '" << identifier << "' but no type resolved";
				continue;
			}
		}

		std::string arrSize;
		size_t bracketPos = type.find("[");
		if (bracketPos != std::string::npos) {
			arrSize = type.substr(bracketPos, type.length() - bracketPos);
			type = type.substr(0, bracketPos);
		}
		std::string decl = type + " " + _prefix + identifier + arrSize;
		stream << decl << ";" << std::endl;

	}

	// implicit and dynamic types
	std::map<std::string, PromelaCodeAnalyzer::PromelaTypedef>::iterator typeIter = allTypes.types.begin();
	while(typeIter != allTypes.types.end()) {
		if (typeIter->second.occurrences.find(this) == typeIter->second.occurrences.end()) {
			typeIter++;
			continue;
		}

		if (processedIdentifiers.find(typeIter->first) != processedIdentifiers.end()) {
			typeIter++;
			continue;
		}

		if (typeIter->first == "_event"
            || typeIter->first == "config"
            || typeIter->first == "_ioprocessors"
            || typeIter->first == "_SESSIONID"
            || typeIter->first == "_NAME"
            || !std::any_of(typeIter->first.begin(), typeIter->first.end(), ::islower)
            ) {
			typeIter++;
			continue;
		}

		processedIdentifiers.insert(typeIter->first);

		if (typeIter->second.types.size() == 0) {
			stream << "hidden " << declForRange(_prefix + typeIter->first, typeIter->second.minValue, typeIter->second.maxValue) << ";" << std::endl;
		} else {
			stream << "hidden " << _prefix << typeIter->second.name << " " << typeIter->first << ";" << std::endl;
		}
		typeIter++;
	}

}

void ChartToPromela::writeStrings(std::ostream& stream) {
    stream << "/* states, events and string literals */" << std::endl;
    std::set<std::string> literals = _analyzer.getLiterals();
    
    {
        for (size_t i = 0; i < _states.size(); i++) {
            if (HAS_ATTR(_states[i], "id")) {
                stream << "#define " << _prefix << _analyzer.macroForLiteral(ATTR(_states[i], "id")) << " " << toStr(i);
                stream << " /* index for state " << ATTR(_states[i], "id") << " */" << std::endl;
            }
        }
    }

    
    for (auto literal : literals) {
        stream << "#define " << _analyzer.macroForLiteral(literal) << " " << _analyzer.indexForLiteral(literal) << " /* " << literal << " */" << std::endl;
    }
}

void ChartToPromela::writeTransitions(std::ostream& stream) {
	for (size_t i = 0; i < _transitions.size(); i++) {
		DOMElement* transition(_transitions[i]);

		/** source */
		stream << "  " << _prefix << "transitions[" << toStr(i) << "].source = ";
		stream << ATTR_CAST(transition->getParentNode(), "documentOrder") ;
		stream << ";" << std::endl;

		/** target */
		if (HAS_ATTR(transition, "targetBools")) {
			std::string targetBools = ATTR(transition, "targetBools");
			for (size_t j = 0; j < _states.size(); j++) {
				if (targetBools[j] == '1')
					stream << "  " << _prefix << "transitions[" << toStr(i) << "].target[" << toStr(j) << "] = 1;" << std::endl;
			}
		}

#if 0
        /** events */
		if (HAS_ATTR(transition, "event")) {
			std::list<std::string> events = tokenize(ATTR(transition, "event"), ' ', true);
			for(auto& event : events) {
				auto trieNodes = _analyzer.getTrie().getWordsWithPrefix(event);
				for(auto trieNode : trieNodes) {
					stream << "  " << _prefix << "transitions[" << toStr(i) << "].event[" << _analyzer.macroForLiteral(trieNode->value) << "] = 1;" << std::endl;
				}
			}
		}
#endif
        
		if (!HAS_ATTR(transition, "event"))
			stream << "  " << _prefix << "transitions[" << toStr(i) << "].type[USCXML_TRANS_SPONTANEOUS] = 1;" << std::endl;

		if (!HAS_ATTR(transition, "target"))
			stream << "  " << _prefix << "transitions[" << toStr(i) << "].type[USCXML_TRANS_TARGETLESS] = 1;" << std::endl;

		if (HAS_ATTR(transition, "type") && ATTR(transition, "type") == "internal")
			stream << "  " << _prefix << "transitions[" << toStr(i) << "].type[USCXML_TRANS_INTERNAL] = 1;" << std::endl;

		if (TAGNAME_CAST(transition->getParentNode()) == XML_PREFIX(transition).str() + "history")
			stream << "  " << _prefix << "transitions[" << toStr(i) << "].type[USCXML_TRANS_HISTORY] = 1;" << std::endl;

		if (TAGNAME_CAST(transition->getParentNode()) == XML_PREFIX(transition).str() + "initial")
			stream << "  " << _prefix << "transitions[" << toStr(i) << "].type[USCXML_TRANS_INITIAL] = 1;" << std::endl;

		if (HAS_ATTR(transition, "conflictBools")) {
			std::string conflicts = ATTR(transition, "conflictBools");
			for (auto j = 0; j < conflicts.size(); j++) {
				if (conflicts[j] == '1')
					stream << "  " << _prefix << "transitions[" << toStr(i) << "].conflicts[" << toStr(j) << "] = 1;" << std::endl;
			}
		}

		if (HAS_ATTR(transition, "exitSetBools")) {
			std::string exitSet = ATTR(transition, "exitSetBools");
			for (auto j = 0; j < exitSet.size(); j++) {
				if (exitSet[j] == '1')
					stream << "  " << _prefix << "transitions[" << toStr(i) << "].exit_set[" << toStr(j) << "] = 1;" << std::endl;
			}
		}

		stream << std::endl;

	}
}



void ChartToPromela::writeStates(std::ostream& stream) {
	for (size_t i = 0; i < _states.size(); i++) {
		DOMElement* state(_states[i]);

		stream << "  " << _prefix << "states[" << toStr(i) << "].parent = ";
		stream << (i == 0 ? "0" : ATTR_CAST(state->getParentNode(), "documentOrder"));
		stream << ";" << std::endl;


		if (HAS_ATTR(state, "childBools")) {
			std::string childs = ATTR(state, "childBools");
			for (auto j = 0; j < childs.size(); j++) {
				if (childs[j] == '1')
					stream << "  " << _prefix << "states[" << toStr(i) << "].children[" << toStr(j) << "] = 1;" << std::endl;
			}
		}

		if (HAS_ATTR(state, "completionBools")) {
			std::string completions = ATTR(state, "completionBools");
			for (auto j = 0; j < completions.size(); j++) {
				if (completions[j] == '1')
					stream << "  " << _prefix << "states[" << toStr(i) << "].completion[" << toStr(j) << "] = 1;" << std::endl;
			}
		}

		if (HAS_ATTR(state, "ancBools")) {
			std::string ancestors = ATTR(state, "ancBools");
			for (auto j = 0; j < ancestors.size(); j++) {
				if (ancestors[j] == '1')
					stream << "  " << _prefix << "states[" << toStr(i) << "].ancestors[" << toStr(j) << "] = 1;" << std::endl;
			}
		}
		if (false) {
		} else if (iequals(TAGNAME(state), "initial")) {
			stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_INITIAL] = 1;" << std::endl;
		} else if (isFinal(state)) {
			stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_FINAL] = 1;" << std::endl;
		} else if (isHistory(state)) {
			if (HAS_ATTR(state, "type") && iequals(ATTR(state, "type"), "deep")) {
				stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_HISTORY_DEEP] = 1;" << std::endl;
			} else {
				stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_HISTORY_SHALLOW] = 1;" << std::endl;
			}
		} else if (isAtomic(state)) {
			stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_ATOMIC] = 1;" << std::endl;
		} else if (isParallel(state)) {
			stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_PARALLEL] = 1;" << std::endl;
		} else if (isCompound(state)) {
			stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_COMPOUND] = 1;" << std::endl;
		} else { // <scxml>
			stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_COMPOUND] = 1;" << std::endl;
		}
		if (HAS_ATTR(state, "hasHistoryChild")) {
			stream << "  " << _prefix << "states[" << toStr(i) << "].type[USCXML_STATE_HAS_HISTORY] = 1;" << std::endl;
		}

		stream << std::endl;

	}
}


void ChartToPromela::writeHelpers(std::ostream& stream) {


}

void ChartToPromela::writeExecContent(std::ostream& stream, const XERCESC_NS::DOMNode* node, size_t indent) {
	if (!node)
		return;

	std::string padding;
	for (size_t i = 0; i < indent; i++) {
		padding += "  ";
	}

	if (node->getNodeType() == DOMNode::TEXT_NODE) {
		if (boost::trim_copy(X(node->getNodeValue()).str()).length() > 0)
			stream << beautifyIndentation(ADAPT_SRC(X(node->getNodeValue()).str()), indent) << std::endl;
	}

	if (node->getNodeType() != DOMNode::ELEMENT_NODE)
		return; // skip anything not an element

	const XERCESC_NS::DOMElement* element = static_cast<const XERCESC_NS::DOMElement*>(node);

	if (false) {
	} else if(TAGNAME(element) == "onentry" ||
	          TAGNAME(element) == "onexit" ||
	          TAGNAME(element) == "transition" ||
	          TAGNAME(element) == "finalize") {
		// descent into childs and write their contents
		const XERCESC_NS::DOMNode* child = node->getFirstChild();
		while(child) {
			writeExecContent(stream, child, indent);
			child = child->getNextSibling();
		}
	} else if(TAGNAME(element) == "script") {
		std::list<DOMNode*> scriptTexts = DOMUtils::filterChildType(DOMNode::TEXT_NODE, node, true);
		for (auto scriptText : scriptTexts) {
			stream << ADAPT_SRC(beautifyIndentation(X(scriptText->getNodeValue()).str(), indent)) << std::endl;
		}

	} else if(TAGNAME(element) == "log") {
		std::string label = (HAS_ATTR(element, "label") ? ATTR(element, "label") : "");
		std::string expr = (HAS_ATTR(element, "expr") ? ADAPT_SRC(ATTR(element, "expr")) : "");
		std::string trimmedExpr = boost::trim_copy(expr);
		bool isStringLiteral = (boost::starts_with(trimmedExpr, "\"") || boost::starts_with(trimmedExpr, "'"));

		std::string formatString;
		std::string varString;
		std::string seperator;

		if (label.size() > 0) {
			if (expr.size() > 0) {
				formatString += label + ": ";
			} else {
				formatString += label;
			}
		}

		if (isStringLiteral) {
			formatString += expr;
		} else if (expr.size() > 0) {
			formatString += "%d";
			varString += seperator + expr;
		}

		if (varString.length() > 0) {
			stream << padding << "printf(\"" + formatString + "\", " + varString + ");" << std::endl;
		} else {
			stream << padding << "printf(\"" + formatString + "\");" << std::endl;
		}

	} else if(TAGNAME(element) == "foreach") {
		stream << padding << "for (" << _prefix << (HAS_ATTR(element, "index") ? ATTR(element, "index") : "_index") << " in " << _prefix << ATTR(element, "array") << ") {" << std::endl;
		if (HAS_ATTR(element, "item")) {
			stream << padding << "  " << _prefix << ATTR(element, "item") << " = " << _prefix << ATTR(element, "array") << "[" << _prefix << (HAS_ATTR(element, "index") ? ATTR(element, "index") : "_index") << "];" << std::endl;
		}
		const XERCESC_NS::DOMNode* child = element->getFirstChild();
		while(child) {
			writeExecContent(stream, child, indent + 1);
			child = child->getNextSibling();
		}
		//		if (HAS_ATTR(nodeElem, "index"))
		//			stream << padding << "  " << _prefix << ATTR(nodeElem, "index") << "++;" << std::endl;
		stream << padding << "}" << std::endl;

	} else if(TAGNAME(element) == "if") {
		std::list<DOMElement*> condChain;
		condChain.push_back(const_cast<DOMElement*>(element));

		condChain.splice(condChain.end(), DOMUtils::filterChildElements(XML_PREFIX(element).str() + "elseif", element));
		condChain.splice(condChain.end(), DOMUtils::filterChildElements(XML_PREFIX(element).str() + "else", element));

		writeIfBlock(stream, condChain, indent);

	} else if(TAGNAME(element) == "assign") {
        
        std::list<DOMNode*> assignTexts = DOMUtils::filterChildType(DOMNode::TEXT_NODE, element, true);
        assert(assignTexts.size() > 0);
        stream << beautifyIndentation(ADAPT_SRC(boost::trim_copy(X(assignTexts.front()->getNodeValue()).str())), indent) << std::endl;
        
	} else if(TAGNAME(element) == "send" || TAGNAME(element) == "raise") {
		std::string targetQueue;
		std::string insertOp = "!";
		if (TAGNAME(element) == "raise") {
			targetQueue = _prefix + "iQ";
		} else if (!HAS_ATTR(element, "target")) {
//      if (_allowEventInterleaving) {
//        targetQueue = _prefix + "tmpQ";
//      } else {
			targetQueue = _prefix + "eQ";
//      }
		} else if (ATTR(element, "target").compare("#_internal") == 0) {
			targetQueue = _prefix + "iQ";
		} else if (ATTR(element, "target").compare("#_parent") == 0) {
			targetQueue = _parent->_prefix + "eQ";
		} else if (boost::starts_with(ATTR(element, "target"), "#_") && _machinesPerId.find(ATTR(element, "target").substr(2)) != _machinesPerId.end()) {
			targetQueue = _machines[_machinesPerId[ATTR(element, "target").substr(2)]]->_prefix + "eQ";
		}
		if (targetQueue.length() > 0) {
			// this is for our external queue
			std::string event;

			if (HAS_ATTR(element, "event")) {
				event = _analyzer.macroForLiteral(ATTR(element, "event"));
			} else if (HAS_ATTR(element, "eventexpr")) {
				event = ADAPT_SRC(ATTR(element, "eventexpr"));
			}
			if (_analyzer.usesComplexEventStruct()) {
				stream << padding << "{" << std::endl;
				std::string typeReset = _analyzer.getTypeReset(_prefix + "_event", _analyzer.getType("_event"), padding + "  ");
				std::stringstream typeAssignSS;
				typeAssignSS << padding << "  " << _prefix << EVENT_NAME << " = " << event << ";" << std::endl;

				if (HAS_ATTR(element, "idlocation")) {
					typeAssignSS << padding << "  /* idlocation */" << std::endl;
					typeAssignSS << padding << "  _lastSendId = _lastSendId + 1;" << std::endl;
					typeAssignSS << padding << "  " << _prefix << ATTR(element, "idlocation") << " = _lastSendId;" << std::endl;
					typeAssignSS << padding << "  " << _prefix << "_event.sendid = _lastSendId;" << std::endl;
					typeAssignSS << padding << "  if" << std::endl;
					typeAssignSS << padding << "  :: _lastSendId == 2147483647 -> _lastSendId = 0;" << std::endl;
					typeAssignSS << padding << "  :: else -> skip;" << std::endl;
					typeAssignSS << padding << "  fi;" << std::endl;
				} else if (HAS_ATTR(element, "id")) {
					typeAssignSS << padding << "  " << _prefix << "_event.sendid = " << _analyzer.macroForLiteral(ATTR(element, "id")) << ";" << std::endl;
				}

				if (_invokerid.length() > 0) { // do not send invokeid if we send / raise to ourself
					typeAssignSS << padding << "  " << _prefix << "_event.invokeid = " << _analyzer.macroForLiteral(_invokerid) << ";" << std::endl;
				}

				if (_analyzer.usesEventField("origintype") && !boost::ends_with(targetQueue, "iQ")) {
					typeAssignSS << padding << "  " << _prefix << "_event.origintype = " << _analyzer.macroForLiteral("http://www.w3.org/TR/scxml/#SCXMLEventProcessor") << ";" << std::endl;
				}

				if (_analyzer.usesEventField("delay")) {
#if NEW_DELAY_RESHUFFLE
#else
					insertOp += "!";
					typeAssignSS << padding << "  _lastSeqId = _lastSeqId + 1;" << std::endl;
#endif
					if (HAS_ATTR_CAST(element, "delay")) {
						typeAssignSS << padding << "  " << _prefix << "_event.delay = " << ATTR_CAST(element, "delay") << ";" << std::endl;
					} else if (HAS_ATTR_CAST(element, "delayexpr")) {
						typeAssignSS << padding << "  " << _prefix << "_event.delay = " << ADAPT_SRC(ATTR_CAST(element, "delayexpr")) << ";" << std::endl;
					} else {
						typeAssignSS << padding << "  " << _prefix << "_event.delay = 0;" << std::endl;
					}
#if NEW_DELAY_RESHUFFLE
#else
					typeAssignSS << padding << "  " << _prefix << "_event.seqNr = _lastSeqId;" << std::endl;
#endif
				}

				if (_analyzer.usesEventField("type")) {
					std::string eventType = (targetQueue.compare("iQ!") == 0 ? _analyzer.macroForLiteral("internal") : _analyzer.macroForLiteral("external"));
					typeAssignSS << padding << "  " << _prefix << "_event.type = " << eventType << ";" << std::endl;
				}

				std::list<DOMElement*> sendParams = DOMUtils::filterChildElements(XML_PREFIX(element).str() + "param", element);
				std::list<DOMElement*> sendContents = DOMUtils::filterChildElements(XML_PREFIX(element).str() + "content", element);
				std::string sendNameList = ATTR(element, "namelist");
				if (sendParams.size() > 0) {
					for (auto sendParam : sendParams) {
						typeAssignSS << padding << "  " << _prefix << "_event.data." << ATTR(sendParam, "name") << " = " << ADAPT_SRC(ATTR(sendParam, "expr"))  << ";" << std::endl;
					}
				}
				if (sendNameList.size() > 0) {
					std::list<std::string> nameListIds = tokenize(sendNameList);
					std::list<std::string>::iterator nameIter = nameListIds.begin();
					while(nameIter != nameListIds.end()) {
						typeAssignSS << padding << "  " << _prefix << "_event.data." << *nameIter << " = " << ADAPT_SRC(*nameIter) << ";" << std::endl;
						nameIter++;
					}
				}

				if (sendParams.size() == 0 && sendNameList.size() == 0 && sendContents.size() > 0) {
					DOMElement* contentElem = sendContents.front();
					if (contentElem->hasChildNodes() && contentElem->getFirstChild()->getNodeType() == DOMNode::TEXT_NODE) {
						std::string content = spaceNormalize(X(contentElem->getFirstChild()->getNodeValue()).str());
						if (!isNumeric(content.c_str(), 10)) {
							typeAssignSS << padding << "  " << _prefix << "_event.data = " << _analyzer.macroForLiteral(content) << ";" << std::endl;
						} else {
							typeAssignSS << padding << "  " << _prefix << "_event.data = " << content << ";" << std::endl;
						}
					} else if (HAS_ATTR(contentElem, "expr")) {
						typeAssignSS << padding << "  " << _prefix << "_event.data = " << ADAPT_SRC(ATTR(contentElem, "expr")) << ";" << std::endl;
					}
				}

				// remove all fields from typeReset that are indeed set by typeAssign
				//        for (std::string assigned; std::getline(typeAssignSS, assigned); ) {
				//          assigned = assigned.substr(0, assigned.find('='));
				//          assigned = assigned.substr(assigned.find('.'));
				//          std::istringstream typeResetSS (typeReset);
				//          for (std::string reset; std::getline(typeResetSS, reset); ) {
				//            if (!boost::find_first(reset, assigned)) {
				//              stream << reset << std::endl;
				//            }
				//          }
				//        }
				//        stream << typeAssignSS.str();

				std::istringstream typeResetSS (typeReset);
				for (std::string reset; std::getline(typeResetSS, reset); ) {
					std::string resetField = reset.substr(0, reset.find('='));
					resetField = resetField.substr(resetField.find('.'));
					for (std::string assigned; std::getline(typeAssignSS, assigned); ) {
						if (boost::find_first(resetField, assigned)) {
							break;
						}
					}
					stream << reset << std::endl;
				}
				stream << typeAssignSS.str();


				stream << padding << "  " << targetQueue << insertOp << _prefix <<"_event;" << std::endl;

#if NEW_DELAY_RESHUFFLE
				if (_analyzer->usesEventField("delay") && !boost::ends_with(targetQueue, "iQ")) {
					stream << padding << "  insertWithDelay(" << targetQueue << ");" << std::endl;
				}
#endif

				stream << padding << "}" << std::endl;
			} else {
				stream << padding << targetQueue << insertOp << event << ";" << std::endl;
			}
		}
	} else if(TAGNAME(element) == "cancel") {
		if (HAS_ATTR(element, "sendid")) {
			stream << padding << "cancelSendId(" << _analyzer.macroForLiteral(ATTR(element, "sendid")) << ", " << (_invokerid.size() > 0 ? _analyzer.macroForLiteral(_invokerid) : "0") << ");" << std::endl;
		} else if (HAS_ATTR(element, "sendidexpr")) {
			stream << padding << "cancelSendId(" << ADAPT_SRC(ATTR(element, "sendidexpr")) << ", " << (_invokerid.size() > 0 ? _analyzer.macroForLiteral(_invokerid) : "0") << ");" << std::endl;
		}
	} else {
		std::cerr << "'" << TAGNAME(element) << "' not supported" << std::endl << element << std::endl;
		assert(false);
	}


}



void ChartToPromela::writeFSM(std::ostream& stream) {
	stream << "/* machine microstep function */" << std::endl;
	stream << "#define USCXML_NUMBER_STATES " << _states.size() << std::endl;
	stream << "#define USCXML_NUMBER_TRANS " << _transitions.size() << std::endl;

	stream << "proctype " << _prefix << "step() { atomic {" << std::endl;
	stream << std::endl;
    stream << "/* ---------------------------- */" << std::endl;
	stream << "MICROSTEP:" << std::endl;

	stream << "do" << std::endl;
	stream << ":: !" << _prefix << "flags[USCXML_CTX_FINISHED] -> {" << std::endl;
	stream << std::endl;

	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Taking a step\\n\");" << std::endl;
	stream << "#endif" << std::endl;


	size_t largestBitWidth = (_states.size() > _transitions.size() ?
	                          BIT_WIDTH(_states.size() + 1) :
	                          BIT_WIDTH(_transitions.size() + 1));
    
	stream << "  unsigned";
	stream << " i : " <<  largestBitWidth << ", ";
	stream << " j : " <<  largestBitWidth << ", ";
	stream << " k : " <<  largestBitWidth << ";" << std::endl;

	stream << "  int err = USCXML_ERR_OK;" << std::endl;

	stream << "  bool conflicts[" << _transitions.size() << "];" << std::endl;
	stream << "  bool trans_set[" << _transitions.size() << "];" << std::endl;

	stream << "  bool target_set[" << _states.size() << "];" << std::endl;
	stream << "  bool exit_set[" << _states.size() << "];" << std::endl;
	stream << "  bool entry_set[" << _states.size() << "];" << std::endl;
	stream << "  bool tmp_states[" << _states.size() << "];" << std::endl;
	stream << std::endl;

#if 0
	stream << "  if" << std::endl;
	stream << "  :: " << _prefix << "flags[USCXML_CTX_FINISHED]" << std::endl;
	stream << "  ACCEPT: {" << std::endl;
	stream << "    false;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> skip;" << std::endl;
	stream << "  fi;" << std::endl;
	stream << std::endl;

	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Machine not finished\\n\");" << std::endl;
	stream << "#endif" << std::endl;
#endif

#if 0
	stream << "  if (ctx->flags & USCXML_CTX_TOP_LEVEL_FINAL) -> {" << std::endl;
	stream << "    /* exit all remaining states */" << std::endl;
	stream << "    i = USCXML_NUMBER_STATES;" << std::endl;
	stream << "    while(i-- > 0) {" << std::endl;
	stream << "      if (BIT_HAS(i, ctx->config)) {" << std::endl;
	stream << "        /* call all on exit handlers */" << std::endl;
	stream << "        if (USCXML_GET_STATE(i).on_exit != NULL) {" << std::endl;
	stream << "          if unlikely((err = USCXML_GET_STATE(i).on_exit(ctx, &USCXML_GET_STATE(i), ctx->event)) != USCXML_ERR_OK)" << std::endl;
	stream << "            return err;" << std::endl;
	stream << "        }" << std::endl;
	//	stream << "        BIT_CLEAR(i, ctx->config);" << std::endl;
	stream << "      }" << std::endl;
	stream << "      if (BIT_HAS(i, ctx->invocations)) {" << std::endl;
	stream << "        if (USCXML_GET_STATE(i).invoke != NULL)" << std::endl;
	stream << "          USCXML_GET_STATE(i).invoke(ctx, &USCXML_GET_STATE(i), NULL, 1);" << std::endl;
	stream << "        BIT_CLEAR(i, ctx->invocations);" << std::endl;
	stream << "      }" << std::endl;
	stream << "    }" << std::endl;
	stream << "    ctx->flags |= USCXML_CTX_FINISHED;" << std::endl;
	stream << "    return USCXML_ERR_DONE;" << std::endl;
	stream << "  }" << std::endl;
	stream << std::endl;

#endif

	stream << "  if" << std::endl;
	stream << "  ::" << _prefix << "flags[USCXML_CTX_TOP_LEVEL_FINAL] -> {" << std::endl;
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Top level final state reached\\n\");" << std::endl;
	stream << "#endif" << std::endl;
	stream << "    /* exit all remaining states */" << std::endl;
	stream << "    i = USCXML_NUMBER_STATES;" << std::endl;
	stream << "    do" << std::endl;
	stream << "    :: i > 0 -> {" << std::endl;
	stream << "      i = i - 1;" << std::endl;
	stream << "      if" << std::endl;
	stream << "      :: " << _prefix << "config[i] -> {" << std::endl;
	stream << "        /* TODO: call all on exit handlers */" << std::endl;
	stream << "        skip;" << std::endl;
	stream << "        " << std::endl;
	stream << "      }" << std::endl;
	stream << "      :: else -> skip;" << std::endl;
	stream << "      fi;" << std::endl;
	stream << std::endl;

	stream << "      if" << std::endl;
	stream << "      :: " << _prefix << "invocations[i] -> {" << std::endl;
	stream << "        /* TODO: cancel invocations */" << std::endl;
	stream << "        skip;" << std::endl;
	stream << "        " << std::endl;
	stream << "      }" << std::endl;
	stream << "      :: else -> skip;" << std::endl;
	stream << "      fi;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    :: else -> break;" << std::endl;
	stream << "    od;" << std::endl;
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Ending machine!\\n\");" << std::endl;
	stream << "#endif" << std::endl;
	stream << "    " << _prefix << "flags[USCXML_CTX_FINISHED] = true;" << std::endl;
	stream << "    goto MICROSTEP;" << std::endl;

	stream << "  }" << std::endl;
	stream << "  :: else -> skip;" << std::endl;
	stream << "  fi;" << std::endl;
	stream << std::endl;

#if 0
	stream << "  bit_clear_all(target_set, nr_states_bytes);" << std::endl;
	stream << "  bit_clear_all(trans_set, nr_trans_bytes);" << std::endl;
	stream << "  if unlikely(ctx->flags == USCXML_CTX_PRISTINE) {" << std::endl;
	stream << "    if (ctx->machine->script != NULL)" << std::endl;
	stream << "      ctx->machine->script(ctx, &ctx->machine->states[0], NULL);" << std::endl;
	stream << "    bit_or(target_set, ctx->machine->states[0].completion, nr_states_bytes);" << std::endl;
	stream << "    ctx->flags |= USCXML_CTX_SPONTANEOUS | USCXML_CTX_INITIALIZED;" << std::endl;
	stream << "    goto ESTABLISH_ENTRY_SET;" << std::endl;
	stream << "  }" << std::endl;
	stream << std::endl;
#endif

	stream << "  if" << std::endl;
	stream << "  ::" << _prefix << "flags[USCXML_CTX_PRISTINE] -> {" << std::endl;
	stream << "    /* run global scripts */" << std::endl;
    
    std::list<DOMElement*> globalScripts = DOMUtils::filterChildElements(XML_PREFIX(_scxml).str() + "script", _scxml, false);
    for (auto globalScript : globalScripts) {
        writeExecContent(stream, globalScript);
    }
    stream << std::endl;

	stream << "    /* Enter initial configuration */" << std::endl;
	bit_copy(stream, _prefix + "states[0].completion", "target_set", _states.size(), 2);
	stream << "    " << _prefix << "flags[USCXML_CTX_SPONTANEOUS] = true;" << std::endl;
	stream << "    " << _prefix << "flags[USCXML_CTX_PRISTINE] = false;" << std::endl;

	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Entering initial default completion\\n\");" << std::endl;
	stream << "#endif" << std::endl;

	stream << "    goto ESTABLISH_ENTRY_SET;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> skip;" << std::endl;
	stream << "  fi;" << std::endl;
	stream << std::endl;


#if 0
	stream << "DEQUEUE_EVENT:" << std::endl;
	stream << "  if (ctx->flags & USCXML_CTX_SPONTANEOUS) {" << std::endl;
	stream << "    ctx->event = NULL;" << std::endl;
	stream << "    goto SELECT_TRANSITIONS;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  if (ctx->dequeue_internal != NULL && (ctx->event = ctx->dequeue_internal(ctx)) != NULL) {" << std::endl;
	stream << "    goto SELECT_TRANSITIONS;" << std::endl;
	stream << "  }" << std::endl;
	stream << std::endl;
#endif


    stream << "/* ---------------------------- */" << std::endl;
	stream << "DEQUEUE_EVENT:" << std::endl;
	stream << "  if" << std::endl;
	stream << "  ::" << _prefix << "flags[USCXML_CTX_SPONTANEOUS] -> {" << std::endl;
	stream << "    " << _prefix << EVENT_NAME << " = USCXML_EVENT_SPONTANEOUS;" << std::endl;
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Trying with a spontaneuous event\\n\");" << std::endl;
	stream << "#endif" << std::endl;
	stream << "    goto SELECT_TRANSITIONS;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> skip;" << std::endl;
	stream << "  fi;" << std::endl;
	stream << std::endl;

	stream << "  if" << std::endl;
	stream << "  :: len(" << _prefix << "iQ) != 0 -> {" << std::endl;
	stream << "    " << _prefix << "iQ ? " << _prefix << "_event;" << std::endl;
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Deqeued an internal event\\n\");" << std::endl;
	stream << "#endif" << std::endl;
	stream << "    goto SELECT_TRANSITIONS;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> skip;" << std::endl;
	stream << "  fi;" << std::endl;


#if 0
	stream << "  /* manage invocations */" << std::endl;
	stream << "  for (i = 0; i < USCXML_NUMBER_STATES; i++) {" << std::endl;
	stream << "    /* uninvoke */" << std::endl;
	stream << "    if (!BIT_HAS(i, ctx->config) && BIT_HAS(i, ctx->invocations)) {" << std::endl;
	stream << "      if (USCXML_GET_STATE(i).invoke != NULL)" << std::endl;
	stream << "        USCXML_GET_STATE(i).invoke(ctx, &USCXML_GET_STATE(i), NULL, 1);" << std::endl;
	stream << "      BIT_CLEAR(i, ctx->invocations)" << std::endl;
	stream << "    }" << std::endl;
	stream << "    /* invoke */" << std::endl;
	stream << "    if (BIT_HAS(i, ctx->config) && !BIT_HAS(i, ctx->invocations)) {" << std::endl;
	stream << "      if (USCXML_GET_STATE(i).invoke != NULL)" << std::endl;
	stream << "        USCXML_GET_STATE(i).invoke(ctx, &USCXML_GET_STATE(i), NULL, 0);" << std::endl;
	stream << "      BIT_SET_AT(i, ctx->invocations)" << std::endl;
	stream << "    }" << std::endl;
	stream << "  }" << std::endl;
	stream << std::endl;
#endif

	stream << "  /* manage invocations */" << std::endl;
	stream << "  i = 0;" << std::endl;
	stream << "  do" << std::endl;
	stream << "  :: i < USCXML_NUMBER_STATES -> {" << std::endl;
	stream << "    /* uninvoke */" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: !" << _prefix << "config[i] && " << _prefix << "invocations[i] -> {" << std::endl;
	stream << "      skip;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi;" << std::endl;
	stream << std::endl;

	stream << "    /* invoke */" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: " << _prefix << "config[i] && !" << _prefix << "invocations[i] -> {" << std::endl;
	stream << "      skip;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi;" << std::endl;
	stream << "    i = i + 1;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od;" << std::endl;
	stream << std::endl;

#if 0
	stream << "  if (ctx->dequeue_external != NULL && (ctx->event = ctx->dequeue_external(ctx)) != NULL) {" << std::endl;
	stream << "    goto SELECT_TRANSITIONS;" << std::endl;
	stream << "  }" << std::endl;
	stream << std::endl;
	stream << "  if (ctx->dequeue_external == NULL) {" << std::endl;
	stream << "    return USCXML_ERR_DONE;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  return USCXML_ERR_IDLE;" << std::endl;
	stream << std::endl;
#endif

	stream << "  if" << std::endl;
	stream << "  :: len(" << _prefix << "eQ) != 0 -> {" << std::endl;
	stream << "    " << _prefix << "eQ ? " << _prefix << "_event;" << std::endl;
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Deqeued an external event\\n\");" << std::endl;
	stream << "#endif" << std::endl;
	stream << "    goto SELECT_TRANSITIONS;" << std::endl;
	stream << "  }" << std::endl;
//  stream << "  :: else -> quit;" << std::endl;
	stream << "  fi;" << std::endl;
	stream << std::endl;

#if 0
	stream << "SELECT_TRANSITIONS:" << std::endl;
	stream << "  bit_clear_all(conflicts, nr_trans_bytes);" << std::endl;
    stream << "  bit_clear_all(exit_set, nr_states_bytes);" << std::endl;
	stream << "  for (i = 0; i < USCXML_NUMBER_TRANS; i++) {" << std::endl;
	stream << "    /* never select history or initial transitions automatically */" << std::endl;
	stream << "    if unlikely(USCXML_GET_TRANS(i).type & (USCXML_TRANS_HISTORY | USCXML_TRANS_INITIAL))" << std::endl;
	stream << "      continue;" << std::endl;
	stream << std::endl;
	stream << "    /* is the transition active? */" << std::endl;
	stream << "    if (BIT_HAS(USCXML_GET_TRANS(i).source, ctx->config)) {" << std::endl;
	stream << "      /* is it non-conflicting? */" << std::endl;
	stream << "      if (!BIT_HAS(i, conflicts)) {" << std::endl;
	stream << "        /* is it spontaneous with an event or vice versa? */" << std::endl;
	stream << "        if ((USCXML_GET_TRANS(i).event == NULL && ctx->event == NULL) || " << std::endl;
	stream << "          (USCXML_GET_TRANS(i).event != NULL && ctx->event != NULL)) {" << std::endl;
	stream << "          /* is it enabled? */" << std::endl;
	stream << "          if ((ctx->event == NULL || ctx->is_matched(ctx, &USCXML_GET_TRANS(i), ctx->event) > 0) &&" << std::endl;
	stream << "            (USCXML_GET_TRANS(i).condition == NULL || " << std::endl;
	stream << "             USCXML_GET_TRANS(i).is_enabled(ctx, &USCXML_GET_TRANS(i)) > 0)) {" << std::endl;
	stream << "            /* remember that we found a transition */" << std::endl;
	stream << "            ctx->flags |= USCXML_CTX_TRANSITION_FOUND;" << std::endl;
	stream << std::endl;

	stream << "            /* transitions that are pre-empted */" << std::endl;
	stream << "            bit_or(conflicts, USCXML_GET_TRANS(i).conflicts, nr_trans_bytes);" << std::endl;
	stream << std::endl;
	stream << "            /* states that are directly targeted (resolve as entry-set later) */" << std::endl;
	stream << "            bit_or(target_set, USCXML_GET_TRANS(i).target, nr_states_bytes);" << std::endl;
	stream << std::endl;
	stream << "            /* states that will be left */" << std::endl;
	stream << "            bit_or(exit_set, USCXML_GET_TRANS(i).exit_set, nr_states_bytes);" << std::endl;
	stream << std::endl;
	stream << "            BIT_SET_AT(i, trans_set);" << std::endl;
	stream << "          }" << std::endl;
	stream << "        }" << std::endl;
	stream << "      }" << std::endl;
	stream << "    }" << std::endl;
	stream << "  }" << std::endl;
	stream << "  bit_and(exit_set, ctx->config, nr_states_bytes);" << std::endl;
	stream << std::endl;
#endif

    stream << "/* ---------------------------- */" << std::endl;
	stream << "SELECT_TRANSITIONS:" << std::endl;
    bit_clear_all(stream, "conflicts", _transitions.size(), 1);
    bit_clear_all(stream, "trans_set", _transitions.size(), 1);
	bit_clear_all(stream, "target_set", _states.size(), 1);
    bit_clear_all(stream, "exit_set", _states.size(), 1);
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Establishing optimal transition set for event %d\\n\", " << _prefix << EVENT_NAME << ");" << std::endl;
	stream << "#endif" << std::endl;
	stream << "  " << _prefix << "flags[USCXML_CTX_TRANSITION_FOUND] = false;" << std::endl;
	stream << "  i = 0;" << std::endl;
	stream << "  do" << std::endl;
	stream << "  :: i < USCXML_NUMBER_TRANS -> {" << std::endl;

	stream << "    /* only select non-history, non-initial transitions */" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: !" << _prefix << "transitions[i].type[USCXML_TRANS_HISTORY] &&" << std::endl;
	stream << "       !" << _prefix << "transitions[i].type[USCXML_TRANS_INITIAL] -> {" << std::endl;

	stream << "      if" << std::endl;
	stream << "      :: /* is the transition active? */" << std::endl;
	stream << "         " << _prefix << "config[" << _prefix << "transitions[i].source] && " << std::endl;
    stream << std::endl;
	stream << "         /* is it non-conflicting? */" << std::endl;
	stream << "         !conflicts[i] && " << std::endl;
    stream << std::endl;
	stream << "         /* is it spontaneous with an event or vice versa? */" << std::endl;
	stream << "         ((" << _prefix << EVENT_NAME << " == USCXML_EVENT_SPONTANEOUS && " << std::endl;
	stream << "           " << _prefix << "transitions[i].type[USCXML_TRANS_SPONTANEOUS]) || " << std::endl;
	stream << "          (" << _prefix << EVENT_NAME << " != USCXML_EVENT_SPONTANEOUS && " << std::endl;
	stream << "           !" << _prefix << "transitions[i].type[USCXML_TRANS_SPONTANEOUS])) &&" << std::endl;
    stream << std::endl;
	stream << "         /* is it matching and enabled? */" << std::endl;
	stream << "         (false " << std::endl;


	for (auto i = 0; i < _transitions.size(); i++) {
		stream << "          || (i == " << toStr(i);
		if (HAS_ATTR(_transitions[i], "event") && ATTR(_transitions[i], "event") != "*") {
			stream << " && (false";
			std::list<TrieNode*> events =_analyzer.getTrie().getWordsWithPrefix(ATTR(_transitions[i], "event"));
			for (auto event : events) {
				stream << " || " << _prefix << EVENT_NAME << " == " << _analyzer.macroForLiteral(event->value);
			}
			stream << ")";
		}
		if (HAS_ATTR(_transitions[i], "cond")) {
			stream << " && " << ADAPT_SRC(ATTR(_transitions[i], "cond"));
		}
		stream << ")" << std::endl;
	}

	stream << "         ) -> {" << std::endl;

	stream << "        /* remember that we found a transition */" << std::endl;
	stream << "        " << _prefix << "flags[USCXML_CTX_TRANSITION_FOUND] = true;" << std::endl;
	stream << std::endl;

	stream << "        /* transitions that are pre-empted */" << std::endl;
	bit_or(stream, "conflicts", _prefix + "transitions[i].conflicts", _transitions.size(), 4);
	stream << std::endl;

	stream << "        /* states that are directly targeted (resolve as entry-set later) */" << std::endl;
	bit_or(stream, "target_set", _prefix + "transitions[i].target", _states.size(), 4);
	stream << std::endl;

	stream << "        /* states that will be left */" << std::endl;
	bit_or(stream, "exit_set", _prefix + "transitions[i].exit_set", _states.size(), 4);
	stream << std::endl;

	stream << "        trans_set[i] = true;" << std::endl;


	stream << "      }" << std::endl;
	stream << "      :: else {" << std::endl;
	stream << "        skip;" << std::endl;
	stream << "      }" << std::endl;
	stream << "      fi" << std::endl;
	stream << "    }" << std::endl;
	stream << "    :: else -> break;" << std::endl;
	stream << "    fi" << std::endl;

	stream << "    i = i + 1;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od;" << std::endl;

	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Selected Transitions: \");" << std::endl;
	printBitArray(stream, "trans_set", _transitions.size());
	stream << "printf(\"\\n\");" << std::endl;
	stream << "#endif" << std::endl;

	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Target Set: \");" << std::endl;
	printBitArray(stream, "target_set", _states.size());
	stream << "printf(\"\\n\");" << std::endl;
	stream << "#endif" << std::endl;

#if 0
	stream << "  if (ctx->flags & USCXML_CTX_TRANSITION_FOUND) {" << std::endl;
	stream << "    ctx->flags |= USCXML_CTX_SPONTANEOUS;" << std::endl;
	stream << "    ctx->flags &= ~USCXML_CTX_TRANSITION_FOUND;" << std::endl;
	stream << "  } else {" << std::endl;
	stream << "    ctx->flags &= ~USCXML_CTX_SPONTANEOUS;" << std::endl;
	stream << "    goto DEQUEUE_EVENT;" << std::endl;
	stream << "  }" << std::endl;
	stream << std::endl;
#endif

	stream << "  if" << std::endl;
	stream << "  :: " << _prefix << "flags[USCXML_CTX_TRANSITION_FOUND] -> {" << std::endl;
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Found transitions\\n\");" << std::endl;
	stream << "#endif" << std::endl;
	stream << "    " << _prefix << "flags[USCXML_CTX_SPONTANEOUS] = true;" << std::endl;
	stream << "    " << _prefix << "flags[USCXML_CTX_TRANSITION_FOUND] = false;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else {" << std::endl;
	stream << "    " << _prefix << "flags[USCXML_CTX_SPONTANEOUS] = false;" << std::endl;
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Found NO transitions\\n\");" << std::endl;
	stream << "#endif" << std::endl;
	stream << "    goto DEQUEUE_EVENT;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  fi" << std::endl;
	stream << std::endl;

#if 0
	stream << "/* REMEMBER_HISTORY: */" << std::endl;
	stream << "  for (i = 0; i < USCXML_NUMBER_STATES; i++) {" << std::endl;
	stream << "    if unlikely(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_SHALLOW ||" << std::endl;
	stream << "          USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_DEEP) {" << std::endl;
	stream << "      /* a history state whose parent is about to be exited */" << std::endl;
	stream << "      if unlikely(BIT_HAS(USCXML_GET_STATE(i).parent, exit_set)) {" << std::endl;
	stream << "        bit_copy(tmp_states, USCXML_GET_STATE(i).completion, nr_states_bytes);" << std::endl;
	stream << std::endl;
	stream << "        /* set those states who were enabled */" << std::endl;
	stream << "        bit_and(tmp_states, ctx->config, nr_states_bytes);" << std::endl;
	stream << std::endl;
	stream << "        /* clear current history with completion mask */" << std::endl;
	stream << "        bit_and_not(ctx->history, USCXML_GET_STATE(i).completion, nr_states_bytes);" << std::endl;
	stream << std::endl;
	stream << "        /* set history */" << std::endl;
	stream << "        bit_or(ctx->history, tmp_states, nr_states_bytes);" << std::endl;
	stream << "      }" << std::endl;
	stream << "    }" << std::endl;
	stream << "  }" << std::endl;
	stream << std::endl;
#endif

    stream << "/* ---------------------------- */" << std::endl;
	stream << "/* REMEMBER_HISTORY: */" << std::endl;
	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Save history configurations\\n\");" << std::endl;
	stream << "#endif" << std::endl;
	stream << "  i = 0;" << std::endl;
	stream << "  do" << std::endl;
	stream << "  :: i < USCXML_NUMBER_STATES -> {" << std::endl;

	stream << "  if" << std::endl;
	stream << "  :: " << _prefix << "states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||" << std::endl;
	stream << "     " << _prefix << "states[i].type[USCXML_STATE_HISTORY_DEEP] -> {" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: exit_set[" << _prefix << "states[i].parent] -> {" << std::endl;
	stream << "      /* a history state whose parent is about to be exited */" << std::endl;

	bit_copy(stream, _prefix + "states[i].completion", "tmp_states", _states.size(), 3);
	bit_and(stream, "tmp_states", _prefix + "config", _states.size(), 3);
	bit_and_not(stream, "tmp_states", _prefix + "states[i].completion", _states.size(), 3);
	bit_or(stream, _prefix + "history", "tmp_states", _states.size(), 3);
	stream << std::endl;

	stream << "    }" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> skip;" << std::endl;
	stream << "  fi;" << std::endl;


	stream << "    i = i + 1;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od;" << std::endl;
	stream << std::endl;

#if 0
	stream << "ESTABLISH_ENTRY_SET:" << std::endl;
	stream << "  /* calculate new entry set */" << std::endl;
	stream << "  bit_copy(entry_set, target_set, nr_states_bytes);" << std::endl;
	stream << std::endl;
	stream << "  /* iterate for ancestors */" << std::endl;
	stream << "  for (i = 0; i < USCXML_NUMBER_STATES; i++) {" << std::endl;
	stream << "    if (BIT_HAS(i, entry_set)) {" << std::endl;
	stream << "      bit_or(entry_set, USCXML_GET_STATE(i).ancestors, nr_states_bytes);" << std::endl;
	stream << "    }" << std::endl;
	stream << "  }" << std::endl;
	stream << std::endl;
#endif

    stream << "/* ---------------------------- */" << std::endl;
	stream << "ESTABLISH_ENTRY_SET:" << std::endl;
	stream << "  /* calculate new entry set */" << std::endl;
	bit_copy(stream, "target_set", "entry_set", _states.size(), 1);
	stream << std::endl;

	stream << "  i = 0;" << std::endl;
	stream << "  do" << std::endl;
	stream << "  :: i < USCXML_NUMBER_STATES -> {" << std::endl;

	stream << "    if" << std::endl;
	stream << "    :: entry_set[i] -> {" << std::endl;
	stream << "      /* ancestor completion */" << std::endl;
	bit_or(stream, "entry_set", _prefix + "states[i].ancestors", _states.size(), 3);

	stream << "    }" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi;" << std::endl;

	stream << "    i = i + 1;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od;" << std::endl;
	stream << std::endl;

	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Entry Set (after ancestor completion)\");" << std::endl;
	printBitArray(stream, "entry_set", _states.size());
	stream << "printf(\"\\n\");" << std::endl;
	stream << "#endif" << std::endl;

#if 0
	stream << "  /* iterate for descendants */" << std::endl;
	stream << "  for (i = 0; i < USCXML_NUMBER_STATES; i++) {" << std::endl;
	stream << "    if (BIT_HAS(i, entry_set)) {" << std::endl;
	stream << "      switch (USCXML_STATE_MASK(USCXML_GET_STATE(i).type)) {" << std::endl;
#endif

	stream << "  /* iterate for descendants */" << std::endl;
	stream << "  i = 0;" << std::endl;
	stream << "  do" << std::endl;
	stream << "  :: i < USCXML_NUMBER_STATES -> {" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: entry_set[i] -> {" << std::endl;
	stream << "      if" << std::endl;

#if 0
	stream << "        case USCXML_STATE_PARALLEL: {" << std::endl;
	stream << "          bit_or(entry_set, USCXML_GET_STATE(i).completion, nr_states_bytes);" << std::endl;
	stream << "          break;" << std::endl;
	stream << "        }" << std::endl;
#endif

	stream << "      :: " << _prefix << "states[i].type[USCXML_STATE_PARALLEL] -> {" << std::endl;
	bit_or(stream, "entry_set", _prefix + "states[i].completion", _states.size(), 4);
	stream << "      }" << std::endl;


#if 0
	stream << "        case USCXML_STATE_HISTORY_SHALLOW:" << std::endl;
	stream << "        case USCXML_STATE_HISTORY_DEEP: {" << std::endl;
	stream << "          if (!bit_has_and(USCXML_GET_STATE(i).completion, ctx->history, nr_states_bytes) &&" << std::endl;
	stream << "            !BIT_HAS(USCXML_GET_STATE(i).parent, ctx->config)) {" << std::endl;
	stream << "            /* nothing set for history, look for a default transition */" << std::endl;
	stream << "            for (j = 0; j < USCXML_NUMBER_TRANS; j++) {" << std::endl;
	stream << "              if unlikely(ctx->machine->transitions[j].source == i) {" << std::endl;
	stream << "                bit_or(entry_set, ctx->machine->transitions[j].target, nr_states_bytes);" << std::endl;
	stream << "                if(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_DEEP &&" << std::endl;
	stream << "                   !bit_has_and(ctx->machine->transitions[j].target, USCXML_GET_STATE(i).children, nr_states_bytes)) {" << std::endl;
	stream << "                  for (k = i + 1; k < USCXML_NUMBER_STATES; k++) {" << std::endl;
	stream << "                    if (BIT_HAS(k, ctx->machine->transitions[j].target)) {" << std::endl;
	stream << "                      bit_or(entry_set, ctx->machine->states[k].ancestors, nr_states_bytes);" << std::endl;
	stream << "                      break;" << std::endl;
	stream << "                    }" << std::endl;
	stream << "                  }" << std::endl;
	stream << "                }" << std::endl;
	stream << "                BIT_SET_AT(j, trans_set);" << std::endl;
	stream << "                break;" << std::endl;
	stream << "              }" << std::endl;
	stream << "              /* Note: SCXML mandates every history to have a transition! */" << std::endl;
	stream << "            }" << std::endl;
	stream << "          } else {" << std::endl;
	stream << "            bit_copy(tmp_states, USCXML_GET_STATE(i).completion, nr_states_bytes);" << std::endl;
	stream << "            bit_and(tmp_states, ctx->history, nr_states_bytes);" << std::endl;
	stream << "            bit_or(entry_set, tmp_states, nr_states_bytes);" << std::endl;
	stream << "            if (USCXML_GET_STATE(i).type == (USCXML_STATE_HAS_HISTORY | USCXML_STATE_HISTORY_DEEP)) {" << std::endl;
	stream << "              /* a deep history state with nested histories -> more completion */" << std::endl;
	stream << "              for (j = i + 1; j < USCXML_NUMBER_STATES; j++) {" << std::endl;
	stream << "                if (BIT_HAS(j, USCXML_GET_STATE(i).completion) &&" << std::endl;
	stream << "                  BIT_HAS(j, entry_set) &&" << std::endl;
	stream << "                  (ctx->machine->states[j].type & USCXML_STATE_HAS_HISTORY)) {" << std::endl;
	stream << "                  for (k = j + 1; k < USCXML_NUMBER_STATES; k++) {" << std::endl;
	stream << "                    /* add nested history to entry_set */" << std::endl;
	stream << "                    if ((USCXML_STATE_MASK(ctx->machine->states[k].type) == USCXML_STATE_HISTORY_DEEP ||" << std::endl;
	stream << "                       USCXML_STATE_MASK(ctx->machine->states[k].type) == USCXML_STATE_HISTORY_SHALLOW) &&" << std::endl;
	stream << "                      BIT_HAS(k, ctx->machine->states[j].children)) {" << std::endl;
	stream << "                      /* a nested history state */" << std::endl;
	stream << "                      BIT_SET_AT(k, entry_set);" << std::endl;
	stream << "                    }" << std::endl;
	stream << "                  }" << std::endl;
	stream << "                }" << std::endl;
	stream << "              }" << std::endl;
	stream << "            }" << std::endl;
	stream << "          }" << std::endl;
	stream << "          break;" << std::endl;
	stream << "        }" << std::endl;
#endif


	stream << "      :: " << _prefix << "states[i].type[USCXML_STATE_HISTORY_SHALLOW] ||" << std::endl;
	stream << "         " << _prefix << "states[i].type[USCXML_STATE_HISTORY_DEEP] -> {" << std::endl;
	stream << "        if" << std::endl;
	stream << "        :: !";
	bit_has_and(stream, _prefix + "states[i].completion", _prefix + "history", _states.size(), 5);
	stream << " && !" << _prefix << "config[" << _prefix << "states[i].parent]" << " -> {" << std::endl;
    stream << "          /* nothing set for history, look for a default transition */" << std::endl;
    stream << "          j = 0;" << std::endl;
    stream << "          do" << std::endl;
    stream << "          :: j < USCXML_NUMBER_TRANS -> {" << std::endl;
    stream << "             if" << std::endl;
    stream << "             :: " << _prefix << "transitions[j].source == i -> {" << std::endl;
    
    bit_or(stream, "entry_set", _prefix + "transitions[j].target", _states.size(), 8);
    stream << std::endl;
    stream << "               if" << std::endl;
    stream << "               :: (" << _prefix << "states[i].type[USCXML_STATE_HISTORY_DEEP] &&" << std::endl;
    stream << "                   !";
    bit_has_and(stream, _prefix + "transitions[j].target", _prefix + "states[i].children", _states.size(), 10);
    stream << "                  ) -> {" << std::endl;
    stream << "                 k = i + 1" << std::endl;
    stream << "                 do" << std::endl;
    stream << "                 :: k < USCXML_NUMBER_STATES -> {" << std::endl;
    stream << "                   if" << std::endl;
    stream << "                   :: " << _prefix << "transitions[j].target[k] -> {" << std::endl;
    bit_or(stream, "entry_set", _prefix + "states[k].ancestors", _states.size(), 11);
    stream << "                     break;" << std::endl;
    stream << std::endl;
    stream << "                   }" << std::endl;
    stream << "                   :: else -> skip;" << std::endl;
    stream << "                   fi" << std::endl;
    stream << "                 }" << std::endl;
    stream << "                 :: else -> break;" << std::endl;
    stream << "                 od" << std::endl;
    stream << "                 trans_set[j] = true;" << std::endl;
    stream << "                 break;" << std::endl;
    stream << "               }" << std::endl;
    stream << "               :: else -> skip;" << std::endl;
    stream << "               fi" << std::endl;

    stream << "             }" << std::endl;
    stream << "             :: else -> skip;" << std::endl;
    stream << "             fi" << std::endl;
    stream << "             j = j + 1;" << std::endl;
    stream << "          }" << std::endl;
    stream << "          :: else -> break" << std::endl;
    stream << "          od" << std::endl;
	stream << "          skip;" << std::endl;
	stream << "        }" << std::endl;
    stream << "        :: else -> {" << std::endl;
    bit_copy(stream, "tmp_states", _prefix + "states[i].completion", _states.size(), 5);
    bit_and(stream, "tmp_states", _prefix + "history", _states.size(), 5);
    bit_or(stream, "entry_set", "tmp_states", _states.size(), 5);
    stream << "          if" << std::endl;
    stream << "          :: " << _prefix << "states[i].type[USCXML_STATE_HAS_HISTORY] ||" << std::endl;
    stream << "             " << _prefix << "states[i].type[USCXML_STATE_HISTORY_DEEP] -> { " << std::endl;
    stream << "            /* a deep history state with nested histories -> more completion */" << std::endl;
    stream << "            j = i + 1;" << std::endl;
    stream << "            do" << std::endl;
    stream << "            :: j < USCXML_NUMBER_STATES -> {" << std::endl;
    stream << "              if" << std::endl;
    stream << "              :: (" << _prefix << "states[i].completion[j] &&" << std::endl;
    stream << "                  entry_set[j] && " << std::endl;
    stream << "                  " << _prefix << "states[j].type[USCXML_STATE_HAS_HISTORY]) -> {" << std::endl;
    stream << "                k = j + 1;" << std::endl;
    stream << "                do" << std::endl;
    stream << "                :: k < USCXML_NUMBER_STATES -> {" << std::endl;
    stream << "                  /* add nested history to entry_set */" << std::endl;
    stream << "                  k = k + 1;" << std::endl;
    stream << "                  if" << std::endl;
    stream << "                  :: (" << _prefix << "states[k].type[USCXML_STATE_HISTORY_DEEP] ||" << std::endl;
    stream << "                      " << _prefix << "states[k].type[USCXML_STATE_HISTORY_SHALLOW]) &&" << std::endl;
    stream << "                     " << _prefix << "states[j].children[k] -> {" << std::endl;
    stream << "                    /* a nested history state */" << std::endl;
    stream << "                    entry_set[k] = true;" << std::endl;
    stream << "                  }" << std::endl;
    stream << "                  :: else -> skip;" << std::endl;
    stream << "                  fi" << std::endl;
    stream << "                }" << std::endl;
    stream << "                :: else -> break;" << std::endl;
    stream << "                od" << std::endl;
    stream << "              }" << std::endl;
    stream << "              :: else -> skip;" << std::endl;
    stream << "              fi" << std::endl;
    stream << "            }" << std::endl;
    stream << "            :: else -> break;" << std::endl;
    stream << "            od" << std::endl;
    stream << "          }" << std::endl;
    stream << "          :: else -> skip;" << std::endl;
    stream << "          fi" << std::endl;

    stream << "        }" << std::endl;
	stream << "        fi;" << std::endl;

	stream << "      }" << std::endl;

#if 0
	stream << "        case USCXML_STATE_INITIAL: {" << std::endl;
	stream << "          for (j = 0; j < USCXML_NUMBER_TRANS; j++) {" << std::endl;
	stream << "            if (ctx->machine->transitions[j].source == i) {" << std::endl;
	stream << "              BIT_SET_AT(j, trans_set);" << std::endl;
	stream << "              BIT_CLEAR(i, entry_set);" << std::endl;
	stream << "              bit_or(entry_set, ctx->machine->transitions[j].target, nr_states_bytes);" << std::endl;
	stream << "              for (k = i + 1; k < USCXML_NUMBER_STATES; k++) {" << std::endl;
	stream << "                if (BIT_HAS(k, ctx->machine->transitions[j].target)) {" << std::endl;
	stream << "                  bit_or(entry_set, ctx->machine->states[k].ancestors, nr_states_bytes);" << std::endl;
	stream << "                }" << std::endl;
	stream << "              }" << std::endl;
	stream << "            }" << std::endl;
	stream << "          }" << std::endl;
	stream << "          break;" << std::endl;
	stream << "        }" << std::endl;
#endif

	stream << "      :: " << _prefix << "states[i].type[USCXML_STATE_INITIAL] -> {" << std::endl;
	stream << "        j = 0" << std::endl;
	stream << "        do" << std::endl;
	stream << "        :: j < USCXML_NUMBER_TRANS -> {" << std::endl;
	stream << "          if" << std::endl;
	stream << "          :: " << _prefix << "transitions[j].source == i -> {" << std::endl;
	stream << "            trans_set[j] = true;" << std::endl;
	stream << "            entry_set[i] = false;" << std::endl;

	bit_or(stream, "entry_set", _prefix + "transitions[j].target", _states.size(), 6);
	stream << std::endl;

	stream << "            k = i + 1;" << std::endl;
	stream << "            do" << std::endl;
	stream << "            :: k < USCXML_NUMBER_STATES -> {" << std::endl;
	stream << "              if" << std::endl;
	stream << "              :: " << _prefix << "transitions[j].target[k] -> {" << std::endl;

	bit_or(stream, "entry_set", _prefix + "states[k].ancestors", _states.size(), 8);
	stream << std::endl;

	stream << "              }" << std::endl;
	stream << "              :: else -> break;" << std::endl;
	stream << "              fi" << std::endl;
	stream << "              k = k + 1;" << std::endl;
	stream << "            }" << std::endl;
	stream << "            :: else -> break" << std::endl;
	stream << "            od" << std::endl;
	stream << "          }" << std::endl;
	stream << "          :: else -> break;" << std::endl;
	stream << "          fi" << std::endl;
	stream << "          j = j + 1;" << std::endl;
	stream << "        }" << std::endl;
	stream << "        :: else -> break" << std::endl;
	stream << "        od;" << std::endl;

	stream << "      }" << std::endl;


#if 0
	stream << "        case USCXML_STATE_COMPOUND: { /* we need to check whether one child is already in entry_set */" << std::endl;
	stream << "          if (!bit_has_and(entry_set, USCXML_GET_STATE(i).children, nr_states_bytes) &&" << std::endl;
	stream << "            (!bit_has_and(ctx->config, USCXML_GET_STATE(i).children, nr_states_bytes) ||" << std::endl;
	stream << "             bit_has_and(exit_set, USCXML_GET_STATE(i).children, nr_states_bytes)))" << std::endl;
	stream << "          {" << std::endl;
	stream << "            bit_or(entry_set, USCXML_GET_STATE(i).completion, nr_states_bytes);" << std::endl;
	stream << "            if (!bit_has_and(USCXML_GET_STATE(i).completion, USCXML_GET_STATE(i).children, nr_states_bytes)) {" << std::endl;
	stream << "              /* deep completion */" << std::endl;
	stream << "              for (j = i + 1; j < USCXML_NUMBER_STATES; j++) {" << std::endl;
	stream << "                if (BIT_HAS(j, USCXML_GET_STATE(i).completion)) {" << std::endl;
	stream << "                  bit_or(entry_set, ctx->machine->states[j].ancestors, nr_states_bytes);" << std::endl;
	stream << "                  break; /* completion of compound is single state */" << std::endl;
	stream << "                }" << std::endl;
	stream << "              }" << std::endl;
	stream << "            }" << std::endl;
	stream << "          }" << std::endl;
	stream << "          break;" << std::endl;
	stream << "        }" << std::endl;
	stream << "      }" << std::endl;
	stream << "    }" << std::endl;
	stream << "  }" << std::endl;
	stream << std::endl;
#endif

	stream << "      :: " << _prefix << "states[i].type[USCXML_STATE_COMPOUND] -> {" << std::endl;

	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Descendant completion for compound state %d\\n\", i);" << std::endl;
	stream << "#endif" << std::endl;

	stream << "        /* we need to check whether one child is already in entry_set */" << std::endl;
	stream << "        if" << std::endl;
	stream << "        :: (" << std::endl;
	stream << "          !";
	bit_has_and(stream, "entry_set", _prefix + "states[i].children", _states.size(), 5);
	stream << " && " << std::endl;
	stream << "           (!";
	bit_has_and(stream, _prefix + "config", _prefix + "states[i].children", _states.size(), 5);
	stream << " || " << std::endl;
	bit_has_and(stream, "exit_set", _prefix + "states[i].children", _states.size(), 5);
	stream << ")) "<< std::endl;
	stream << "        -> {" << std::endl;

	bit_or(stream, "entry_set", _prefix + "states[i].completion", _states.size(), 5);

	stream << "             if" << std::endl;
	stream << "             :: (";
	bit_has_and(stream, _prefix + "states[i].completion", _prefix + "states[i].children", _states.size(), 5);
	stream << std::endl;
	stream << "              ) -> {" << std::endl;
	stream << "                /* deep completion */" << std::endl;
	stream << "                j = i + 1;" << std::endl;
	stream << "                do" << std::endl;
	stream << "                :: j < USCXML_NUMBER_STATES - 1 -> {" << std::endl;
	stream << "                  j = j + 1;" << std::endl;
	stream << "                  if" << std::endl;
	stream << "                  :: " << _prefix << "states[i].completion[j] -> {" << std::endl;

	bit_or(stream, "entry_set", _prefix + "states[j].ancestors", _states.size(), 9);
	stream << std::endl;

	stream << "                    /* completion of compound is single state */" << std::endl;
	stream << "                    break;" << std::endl;
	stream << "                  } " << std::endl;
	stream << "                  :: else -> skip;" << std::endl;
	stream << "                  fi" << std::endl;
	stream << "                }" << std::endl;
	stream << "                :: else -> break;" << std::endl;
	stream << "                od" << std::endl;

	stream << "             }" << std::endl;
	stream << "             :: else -> skip;" << std::endl;
	stream << "             fi" << std::endl;

	stream << "        }" << std::endl;
	stream << "        :: else -> skip;" << std::endl;
	stream << "        fi" << std::endl;
	stream << "      }" << std::endl;

	stream << "      :: else -> skip;" << std::endl;
	stream << "      fi;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi;" << std::endl;
	stream << "    i = i + 1;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od;" << std::endl;
	stream << std::endl;

#if 0
	stream << "/* EXIT_STATES: */" << std::endl;
	stream << "  i = USCXML_NUMBER_STATES;" << std::endl;
	stream << "  while(i-- > 0) {" << std::endl;
	stream << "    if (BIT_HAS(i, exit_set) && BIT_HAS(i, ctx->config)) {" << std::endl;
	stream << "      /* call all on exit handlers */" << std::endl;
	stream << "      if (USCXML_GET_STATE(i).on_exit != NULL) {" << std::endl;
	stream << "        if unlikely((err = USCXML_GET_STATE(i).on_exit(ctx, &USCXML_GET_STATE(i), ctx->event)) != USCXML_ERR_OK)" << std::endl;
	stream << "          return err;" << std::endl;
	stream << "      }" << std::endl;
	stream << "      BIT_CLEAR(i, ctx->config);" << std::endl;
	stream << "    }" << std::endl;
	stream << "  }" << std::endl;
	stream << std::endl;
#endif

	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Entry Set (after descendant completion)\");" << std::endl;
	printBitArray(stream, "entry_set", _states.size());
	stream << "printf(\"\\n\");" << std::endl;
	stream << "#endif" << std::endl;

    stream << "/* ---------------------------- */" << std::endl;
	stream << "/* EXIT_STATES: */" << std::endl;
	stream << "  i = USCXML_NUMBER_STATES;" << std::endl;
	stream << "  do" << std::endl;
	stream << "  :: i > 0 -> {" << std::endl;
	stream << "    i = i - 1;" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: exit_set[i] && " << _prefix << "config[i] -> {" << std::endl;
	stream << "      /* call all on-exit handlers */" << std::endl;
    
    stream << "      if" << std::endl;
    for (auto i = 0; i < _states.size(); i++) {
        std::list<DOMElement*> onentries = DOMUtils::filterChildElements(XML_PREFIX(_states[i]).str() + "onexit" , _states[i]);
        if (onentries.size() > 0) {
            stream << "      :: i == " << toStr(i) << " -> {" << std::endl;
            for (auto onentry : onentries)
                writeExecContent(stream, onentry, 3);
            stream << "      }" << std::endl;
        }
    }
    stream << "      :: else ->skip;" << std::endl;
    stream << "      fi" << std::endl;
    stream << std::endl;

    
	stream << "      " << _prefix << "config[i] = false;" << std::endl;
	stream << "      skip;" << std::endl;
	stream << "    }" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od;" << std::endl;
	stream << std::endl;

	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Exited States\\n\");" << std::endl;
	stream << "#endif" << std::endl;

#if 0
	stream << "/* TAKE_TRANSITIONS: */" << std::endl;
	stream << "  for (i = 0; i < USCXML_NUMBER_TRANS; i++) {" << std::endl;
	stream << "    if (BIT_HAS(i, trans_set) && (USCXML_GET_TRANS(i).type & (USCXML_TRANS_HISTORY | USCXML_TRANS_INITIAL)) == 0) {" << std::endl;
	stream << "      /* call executable content in transition */" << std::endl;
	stream << "      if (USCXML_GET_TRANS(i).on_transition != NULL) {" << std::endl;
	stream << "        if unlikely((err = USCXML_GET_TRANS(i).on_transition(ctx," << std::endl;
	stream << "                                        &ctx->machine->states[USCXML_GET_TRANS(i).source]," << std::endl;
	stream << "                                        ctx->event)) != USCXML_ERR_OK)" << std::endl;
	stream << "          return err;" << std::endl;
	stream << "      }" << std::endl;
	stream << "    }" << std::endl;
	stream << "  }" << std::endl;
	stream << std::endl;
#endif

    stream << "/* ---------------------------- */" << std::endl;
    stream << "/* TAKE_TRANSITIONS: */" << std::endl;
	stream << "  i = 0;" << std::endl;
	stream << "  do" << std::endl;
	stream << "  :: i < USCXML_NUMBER_TRANS -> {" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: trans_set[i] && " << std::endl;
	stream << "       !" << _prefix << "transitions[i].type[USCXML_TRANS_HISTORY] && " << std::endl;
	stream << "       !" << _prefix << "transitions[i].type[USCXML_TRANS_INITIAL] -> {" << std::endl;
    stream << "      /* Call executable content in normal transition */" << std::endl;
    stream << "      if" << std::endl;
    for (auto i = 0; i < _transitions.size(); i++) {
        stream << "      :: i == " << toStr(i) << " -> {" << std::endl;
        writeExecContent(stream, _transitions[i], 4);
        stream << "        skip;" << std::endl;
        stream << "      }" << std::endl;
    }
    stream << "      :: else ->skip;" << std::endl;
    stream << "      fi" << std::endl;
    stream << std::endl;
	stream << "    }" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    fi;" << std::endl;
	stream << "    i = i + 1;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od;" << std::endl;
	stream << std::endl;

	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Took Transitions\\n\");" << std::endl;
	stream << "#endif" << std::endl;

#if 0
	stream << "/* ENTER_STATES: */" << std::endl;
	stream << "  for (i = 0; i < USCXML_NUMBER_STATES; i++) {" << std::endl;
	stream << "    if (BIT_HAS(i, entry_set) && !BIT_HAS(i, ctx->config)) {" << std::endl;
	stream << "      /* these are no proper states */" << std::endl;
	stream << "      if unlikely(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_DEEP ||" << std::endl;
	stream << "            USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_HISTORY_SHALLOW ||" << std::endl;
	stream << "            USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_INITIAL)" << std::endl;
	stream << "        continue;" << std::endl;
	stream << std::endl;
#endif

    stream << "/* ---------------------------- */" << std::endl;
	stream << "/* ENTER_STATES: */" << std::endl;
	stream << "  i = 0;" << std::endl;
	stream << "  do" << std::endl;
	stream << "  :: i < USCXML_NUMBER_STATES -> {" << std::endl;
	stream << "    if" << std::endl;
	stream << "    :: (entry_set[i] &&" << std::endl;
	stream << "      !" << _prefix << "config[i] && " << std::endl;
	stream << "      /* these are no proper states */" << std::endl;
	stream << "      !" << _prefix << "states[i].type[USCXML_STATE_HISTORY_DEEP] && " << std::endl;
	stream << "      !" << _prefix << "states[i].type[USCXML_STATE_HISTORY_SHALLOW] && " << std::endl;
	stream << "      !" << _prefix << "states[i].type[USCXML_STATE_INITIAL]" << std::endl;
	stream << "       ) -> {" << std::endl;

#if 0
	stream << "      BIT_SET_AT(i, ctx->config);" << std::endl;
	stream << std::endl;
#endif

	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Entering State %d\\n\", i);" << std::endl;
	stream << "#endif" << std::endl;

	stream << "         " << _prefix << "config[i] = true;" << std::endl;
	stream << std::endl;


#if 0
	stream << "      /* initialize data */" << std::endl;
	stream << "      if (!BIT_HAS(i, ctx->initialized_data)) {" << std::endl;
	stream << "        if unlikely(USCXML_GET_STATE(i).data != NULL && ctx->exec_content_init != NULL) {" << std::endl;
	stream << "          ctx->exec_content_init(ctx, USCXML_GET_STATE(i).data);" << std::endl;
	stream << "        }" << std::endl;
	stream << "        BIT_SET_AT(i, ctx->initialized_data);" << std::endl;
	stream << "      }" << std::endl;
	stream << std::endl;

#endif

	stream << "         if" << std::endl;
	stream << "         :: !" << _prefix << "initialized_data[i] -> {" << std::endl;
	stream << "           /* TODO: late data binding not supported yet */" << std::endl;
	stream << "           " << _prefix << "initialized_data[i] = true;" << std::endl;
	stream << "           skip" << std::endl;
	stream << "         }" << std::endl;
	stream << "         :: else -> skip;" << std::endl;
	stream << "         fi" << std::endl;
	stream << std::endl;

#if 0
	stream << "      if (USCXML_GET_STATE(i).on_entry != NULL) {" << std::endl;
	stream << "        if unlikely((err = USCXML_GET_STATE(i).on_entry(ctx, &USCXML_GET_STATE(i), ctx->event)) != USCXML_ERR_OK)" << std::endl;
	stream << "          return err;" << std::endl;
	stream << "      }" << std::endl;
	stream << std::endl;

#endif

	stream << "         /* Process executable content for entering a state */" << std::endl;
	stream << "         if" << std::endl;
	for (auto i = 0; i < _states.size(); i++) {
		std::list<DOMElement*> onentries = DOMUtils::filterChildElements(XML_PREFIX(_states[i]).str() + "onentry" , _states[i]);
		if (onentries.size() > 0) {
			stream << "         :: i == " << toStr(i) << " -> {" << std::endl;
			for (auto onentry : onentries)
				writeExecContent(stream, onentry, 5);
			stream << "         }" << std::endl;
		}
	}
	stream << "         :: else ->skip;" << std::endl;
	stream << "         fi" << std::endl;
	stream << std::endl;

#if 0
	stream << "      /* take history and initial transitions */" << std::endl;
	stream << "      for (j = 0; j < USCXML_NUMBER_TRANS; j++) {" << std::endl;
	stream << "        if unlikely(BIT_HAS(j, trans_set) &&" << std::endl;
	stream << "              (ctx->machine->transitions[j].type & (USCXML_TRANS_HISTORY | USCXML_TRANS_INITIAL)) &&" << std::endl;
	stream << "              ctx->machine->states[ctx->machine->transitions[j].source].parent == i) {" << std::endl;
	stream << "          /* call executable content in transition */" << std::endl;
	stream << "          if (ctx->machine->transitions[j].on_transition != NULL) {" << std::endl;
	stream << "            if unlikely((err = ctx->machine->transitions[j].on_transition(ctx," << std::endl;
	stream << "                                            &USCXML_GET_STATE(i)," << std::endl;
	stream << "                                            ctx->event)) != USCXML_ERR_OK)" << std::endl;
	stream << "              return err;" << std::endl;
	stream << "          }" << std::endl;
	stream << "        }" << std::endl;
	stream << "      }" << std::endl;
	stream << std::endl;

#endif

	stream << "         /* take history and initial transitions */" << std::endl;
	stream << "         j = 0;" << std::endl;
	stream << "         do" << std::endl;
	stream << "         :: j < USCXML_NUMBER_TRANS -> {" << std::endl;
	stream << "           if" << std::endl;
	stream << "           :: (trans_set[j] &&" << std::endl;
	stream << "              (" << _prefix << "transitions[j].type[USCXML_TRANS_HISTORY] ||" << std::endl;
	stream << "               " << _prefix << "transitions[j].type[USCXML_TRANS_INITIAL]) && " << std::endl;
	stream << "               " << _prefix << "states[" << _prefix << "transitions[j].source].parent == i) -> {" << std::endl;
	stream << "              /* Call executable content in history or initial transition */" << std::endl;
    stream << "              if" << std::endl;
    for (auto i = 0; i < _transitions.size(); i++) {
        stream << "              :: j == " << toStr(i) << " -> {" << std::endl;
        writeExecContent(stream, _transitions[i], 8);
        stream << "                skip;" << std::endl;
        stream << "              }" << std::endl;
    }
    stream << "              :: else ->skip;" << std::endl;
    stream << "              fi" << std::endl;
    stream << std::endl;

	stream << "           }" << std::endl;
	stream << "           :: else -> skip;" << std::endl;
	stream << "           fi" << std::endl;
	stream << "           j = j + 1;" << std::endl;
	stream << "         }" << std::endl;
	stream << "         :: else -> break;" << std::endl;
	stream << "         od" << std::endl;


#if 0
	stream << "      /* handle final states */" << std::endl;
	stream << "      if unlikely(USCXML_STATE_MASK(USCXML_GET_STATE(i).type) == USCXML_STATE_FINAL) {" << std::endl;
#endif

	stream << "         /* handle final states */" << std::endl;
	stream << "         if" << std::endl;
	stream << "         :: " << _prefix << "states[i].type[USCXML_STATE_FINAL] -> {" << std::endl;


#if 0
	stream << "        if unlikely(USCXML_GET_STATE(i).ancestors[0] == 0x01) {" << std::endl;
	stream << "          ctx->flags |= USCXML_CTX_TOP_LEVEL_FINAL;" << std::endl;
	stream << "        } else {" << std::endl;
	stream << "          /* raise done event */" << std::endl;
	stream << "          const uscxml_elem_donedata* donedata = &ctx->machine->donedata[0];" << std::endl;
	stream << "          while(USCXML_ELEM_DONEDATA_IS_SET(donedata)) {" << std::endl;
	stream << "            if unlikely(donedata->source == i)" << std::endl;
	stream << "              break;" << std::endl;
	stream << "            donedata++;" << std::endl;
	stream << "          }" << std::endl;
	stream << "          ctx->raise_done_event(ctx, &ctx->machine->states[USCXML_GET_STATE(i).parent], (USCXML_ELEM_DONEDATA_IS_SET(donedata) ? donedata : NULL));" << std::endl;
	stream << "        }" << std::endl;
#endif

	stream << "           if" << std::endl;
	stream << "           :: " << _prefix << "states[" << _prefix << "states[i].parent].children[1] -> {" << std::endl;
	stream << "            " << _prefix << "flags[USCXML_CTX_TOP_LEVEL_FINAL] = true;" << std::endl;
	stream << "           }" << std::endl;
	stream << "           :: else -> {" << std::endl;
	stream << "             /* TODO: raise done event */" << std::endl;
	stream << "             skip;" << std::endl;
	stream << "           }" << std::endl;
	stream << "           fi" << std::endl;


#if 0
	stream << std::endl;
	stream << "        /**" << std::endl;
	stream << "         * are we the last final state to leave a parallel state?:" << std::endl;
	stream << "         * 1. Gather all parallel states in our ancestor chain" << std::endl;
	stream << "         * 2. Find all states for which these parallels are ancestors" << std::endl;
	stream << "         * 3. Iterate all active final states and remove their ancestors" << std::endl;
	stream << "         * 4. If a state remains, not all children of a parallel are final" << std::endl;
	stream << "         */" << std::endl;
	stream << "        for (j = 0; j < USCXML_NUMBER_STATES; j++) {" << std::endl;
	stream << "          if unlikely(USCXML_STATE_MASK(ctx->machine->states[j].type) == USCXML_STATE_PARALLEL &&" << std::endl;
	stream << "                BIT_HAS(j, USCXML_GET_STATE(i).ancestors)) {" << std::endl;
	stream << "            bit_clear_all(tmp_states, nr_states_bytes);" << std::endl;
	stream << "            for (k = 0; k < USCXML_NUMBER_STATES; k++) {" << std::endl;
	stream << "              if unlikely(BIT_HAS(j, ctx->machine->states[k].ancestors) && BIT_HAS(k, ctx->config)) {" << std::endl;
	stream << "                if (USCXML_STATE_MASK(ctx->machine->states[k].type) == USCXML_STATE_FINAL) {" << std::endl;
	stream << "                  bit_and_not(tmp_states, ctx->machine->states[k].ancestors, nr_states_bytes);" << std::endl;
	stream << "                } else {" << std::endl;
	stream << "                  BIT_SET_AT(k, tmp_states);" << std::endl;
	stream << "                }" << std::endl;
	stream << "              }" << std::endl;
	stream << "            }" << std::endl;
	stream << "            if unlikely(!bit_has_any(tmp_states, nr_states_bytes)) {" << std::endl;
	stream << "              ctx->raise_done_event(ctx, &ctx->machine->states[j], NULL);" << std::endl;
	stream << "            }" << std::endl;
	stream << "          }" << std::endl;
	stream << "        }" << std::endl;
	stream << "      }" << std::endl;
	stream << "    }" << std::endl;
	stream << "  }" << std::endl;
	stream << std::endl;

	stream << "  return USCXML_ERR_OK;" << std::endl;
	stream << "}" << std::endl;
	stream << std::endl;
	stream << std::endl;
#endif

	stream << "           /** TODO:" << std::endl;
	stream << "          * are we the last final state to leave a parallel state?:" << std::endl;
	stream << "          * 1. Gather all parallel states in our ancestor chain" << std::endl;
	stream << "          * 2. Find all states for which these parallels are ancestors" << std::endl;
	stream << "          * 3. Iterate all active final states and remove their ancestors" << std::endl;
	stream << "          * 4. If a state remains, not all children of a parallel are final" << std::endl;
	stream << "          */" << std::endl;


	stream << "         }" << std::endl;
	stream << "         :: else -> skip;" << std::endl;
	stream << "         fi" << std::endl;

	stream << "" << std::endl;

	stream << "    }" << std::endl;
	stream << "    :: else -> skip;" << std::endl;
	stream << "    i = i + 1;" << std::endl;
	stream << "    fi;" << std::endl;
	stream << "  }" << std::endl;
	stream << "  :: else -> break;" << std::endl;
	stream << "  od;" << std::endl;
	stream << std::endl;

	stream << "#if TRACE_EXECUTION" << std::endl;
	stream << "printf(\"Done\\n\");" << std::endl;
	stream << "#endif" << std::endl;

	stream << "}" << std::endl;
	stream << ":: else -> break;" << std::endl;
	stream << "od" << std::endl;


	stream << "} }" << std::endl;
	stream << std::endl;

}

#if 0

void ChartToPromela::writeProgram(std::ostream& stream) {

	_traceTransitions = envVarIsTrue("USCXML_PROMELA_TRANSITION_TRACE");
	_writeTransitionPrintfs = envVarIsTrue("USCXML_PROMELA_TRANSITION_DEBUG");

	if (!HAS_ATTR(_scxml, "datamodel") || ATTR(_scxml, "datamodel") != "promela") {
		LOG(ERROR) << "Can only convert SCXML documents with \"promela\" datamodel";
		return;
	}

	if (HAS_ATTR(_scxml, "binding") && ATTR(_scxml, "binding") != "early") {
		LOG(ERROR) << "Can only convert for early data bindings";
		return;
	}

	//	std::cerr << _scxml << std::endl;

	stream << "/* " << (std::string)_baseURL << " */" << std::endl;
	stream << std::endl;

	initNodes();

	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator nestedIter = _machines.begin(); nestedIter != _machines.end(); nestedIter++) {
		if (nestedIter->second->_start == NULL) {
			nestedIter->second->interpret();
		}
		nestedIter->second->initNodes();
	}

	writeEvents(stream);
	stream << std::endl;
	writeStates(stream);
	stream << std::endl;
	writeStrings(stream);
	stream << std::endl;
	if (_analyzer->usesInPredicate()) {
		writeStateMap(stream);
		stream << std::endl;
	}
	if (_historyMembers.size() > 0) {
		writeHistoryArrays(stream);
		stream << std::endl;
	}
	writeTypeDefs(stream);
	stream << std::endl;
	writeDeclarations(stream);
	stream << std::endl;

	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator nestedIter = _machines.begin(); nestedIter != _machines.end(); nestedIter++) {
		nestedIter->second->writeDeclarations(stream);
		stream << std::endl;
	}

	stream << std::endl << "/* global inline functions */" << std::endl;

	if (_analyzer->usesComplexEventStruct()) {
		stream << "hidden _event_t tmpE;" << std::endl;
	} else {
		stream << "hidden int tmpE;" << std::endl;
	}
	stream << "hidden int tmpIndex;" << std::endl;


#if NEW_DELAY_RESHUFFLE
	if (_analyzer->usesEventField("delay")) {
		writeInsertWithDelay(stream);
		stream << std::endl;
	}
#endif

	if (_analyzer->usesEventField("delay") && _machines.size() > 0) {
		writeDetermineShortestDelay(stream);
		stream << std::endl;
		writeAdvanceTime(stream);
		stream << std::endl;
		writeRescheduleProcess(stream);
		stream << std::endl;
		writeScheduleMachines(stream);
		stream << std::endl;
	}

	{
		NodeSet<std::string> cancels = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "cancel", _scxml, true);
		if (cancels.size() > 0) {
			writeCancelEvents(stream);
			stream << std::endl;
		}
	}
	{
		NodeSet<std::string> invokes = DOMUtils::filterChildElements(_nsInfo.xmlNSPrefix + "invoke", _scxml, true);
		if (invokes.size() > 0 && _analyzer->usesEventField("delay")) {
			writeRemovePendingEventsFromInvoker(stream);
			stream << std::endl;
		}

	}
	stream << std::endl;
	writeEventSources(stream);
	stream << std::endl;
	writeFSM(stream);
	stream << std::endl;
	writeMain(stream);
	stream << std::endl;

	for (std::map<Arabica::DOM::Node<std::string>, ChartToPromela*>::iterator nestedIter = _machines.begin(); nestedIter != _machines.end(); nestedIter++) {
		nestedIter->second->writeFSM(stream);
		stream << std::endl;
	}

	// write ltl expression for success
	std::stringstream acceptingStates;
	std::string seperator;

	for (std::map<std::string, GlobalState*>::iterator stateIter = _activeConf.begin(); stateIter != _activeConf.end(); stateIter++) {
		FlatStateIdentifier flatId(stateIter->first);
		if (std::find(flatId.getActive().begin(), flatId.getActive().end(), "pass") != flatId.getActive().end()) {
			acceptingStates << seperator << _prefix << "s == s" << stateIter->second->activeIndex;
			seperator = " || ";
		}
	}
	if (acceptingStates.str().size() > 0) {
		stream << "ltl { eventually (" << acceptingStates.str() << ") }" << std::endl;
	}
}
#endif

void ChartToPromela::writeIfBlock(std::ostream& stream, std::list<DOMElement*>& condChain, size_t indent) {
	if (condChain.size() == 0)
		return;

	std::string padding;
	for (size_t i = 0; i < indent; i++) {
		padding += "  ";
	}

	bool noNext = condChain.size() == 1;
	bool nextIsElse = false;

	DOMElement* ifNode = condChain.front();
	condChain.pop_front();

	if (condChain.size() > 0) {
		if (TAGNAME_CAST(condChain.front()) == "else") {
			nextIsElse = true;
		}
	}

	stream << padding << "if" << std::endl;
	// we need to nest the elseifs to resolve promela if semantics
	stream << padding << ":: (" << ADAPT_SRC(ATTR(ifNode, "cond")) << ") -> {" << std::endl;

	DOMNode* child;
	if (TAGNAME(ifNode) == "if") {
		child = ifNode->getFirstChild();
	} else {
		child = ifNode->getNextSibling();
	}
	while(child) {
		if (child->getNodeType() == DOMNode::ELEMENT_NODE) {
			DOMElement* childElem = static_cast<DOMElement*>(child);
			if (TAGNAME(childElem) == "elseif" || TAGNAME_CAST(childElem) == "else")
				break;
			writeExecContent(stream, childElem, indent + 1);
		}
		child = child->getNextSibling();
	}
	stream << padding << "}" << std::endl;
	stream << padding << ":: else -> ";

	if (nextIsElse) {
		child = condChain.front()->getNextSibling();
		stream << "{" << std::endl;
		while(child) {
			if (child->getNodeType() == DOMNode::ELEMENT_NODE) {
				writeExecContent(stream, child, indent + 1);
			}
			child = child->getNextSibling();
		}
		stream << padding << "}" << std::endl;

	} else if (noNext) {
		stream << "skip;" << std::endl;
	} else {
		stream << "{" << std::endl;
		writeIfBlock(stream, condChain, indent + 1);
		stream << padding << "}" << std::endl;
	}

	stream << padding << "fi;" << std::endl;

}

std::string ChartToPromela::beautifyIndentation(const std::string& code, size_t indent) {

	std::string padding;
	for (size_t i = 0; i < indent; i++) {
		padding += "  ";
	}

	// remove topmost indentation from every line and reindent
	std::stringstream beautifiedSS;

	std::string initialIndent;
	bool gotIndent = false;
	bool isFirstLine = true;
	std::stringstream ssLine(code);
	std::string line;

	while(std::getline(ssLine, line)) {
		size_t firstChar = line.find_first_not_of(" \t\r\n");
		if (firstChar != std::string::npos) {
			if (!gotIndent) {
				initialIndent = line.substr(0, firstChar);
				gotIndent = true;
			}
			beautifiedSS << (isFirstLine ? "" : "\n") << padding << boost::replace_first_copy(line, initialIndent, "");
			isFirstLine = false;
		}
	}

	return beautifiedSS.str();
}

std::string ChartToPromela::dataToAssignments(const std::string& prefix, const Data& data) {
	std::stringstream retVal;
	if (data.atom.size() > 0) {
		if (data.type == Data::VERBATIM) {
			retVal << prefix << " = " << _analyzer.macroForLiteral(data.atom) << ";" << std::endl;
		} else {
			retVal << prefix << " = " << data.atom << ";" << std::endl;
		}
	} else if (data.compound.size() > 0) {
		for (std::map<std::string, Data>::const_iterator cIter = data.compound.begin(); cIter != data.compound.end(); cIter++) {
			retVal << dataToAssignments(prefix + "." + cIter->first, cIter->second);
		}
	} else if (data.array.size() > 0) {
		size_t index = 0;
		for(std::list<Data>::const_iterator aIter = data.array.begin(); aIter != data.array.end(); aIter++) {
			retVal << dataToAssignments(prefix + "[" + toStr(index) + "]", *aIter);
			index++;
		}
	}
	return retVal.str();
}

std::string ChartToPromela::sanitizeCode(const std::string& code) {
	std::string replaced = code;
	boost::replace_all(replaced, "\"", "'");
	boost::replace_all(replaced, "_sessionid", "_SESSIONID");
	boost::replace_all(replaced, "_name", "_NAME");
	return replaced;
}

std::string ChartToPromela::declForRange(const std::string& identifier, long minValue, long maxValue, bool nativeOnly) {
	//	return "int " + identifier; // just for testing

	// we know nothing about this type
	if (minValue == 0 && maxValue == 0)
		return "int " + identifier;

	if (minValue < 0) {
		// only short or int for negatives
		if (minValue < -32769 || maxValue > 32767)
			return "int " + identifier;
		return "short " + identifier;
	}

	// type is definitely positive
	if (nativeOnly) {
		if (maxValue > 32767)
			return "int " + identifier;
		if (maxValue > 255)
			return "short " + identifier;
		if (maxValue > 1)
			return "byte " + identifier;
		return "bool " + identifier;
	} else {
		return "unsigned " + identifier + " : " + toStr(BIT_WIDTH(maxValue));
	}
}

void ChartToPromela::writeCancelEvents(std::ostream& stream, int indent) {
    std::list<std::string> queues;
    queues.push_back("eQ");
    if (_allowEventInterleaving)
        queues.push_back("tmpQ");
    
    stream << "inline cancelSendId(sendIdentifier, invokerIdentifier) {" << std::endl;
    for (auto machine : *_machinesAll) {
        for (auto queue : queues) {
            stream << "  cancelSendIdOnQueue(sendIdentifier, " << machine.second->_prefix << queue << ", invokerIdentifier);" << std::endl;
        }
    }
    stream << "}" << std::endl;
    stream << std::endl;
    
    
    stream << "inline cancelSendIdOnQueue(sendIdentifier, queue, invokerIdentifier) {" << std::endl;
    stream << "  tmpIndex = 0;" << std::endl;
    //    stream << _analyzer->getTypeReset("tmpE", _analyzer->getType("_event"), "  ");
    stream << "  do" << std::endl;
    stream << "  :: tmpIndex < len(queue) -> {" << std::endl;
    stream << "    queue?tmpE;" << std::endl;
    stream << "    if" << std::endl;
    stream << "    :: tmpE.invokeid != invokerIdentifier || tmpE.sendid != sendIdentifier || tmpE.delay == 0 -> queue!tmpE;" << std::endl;
    stream << "    :: else -> skip;" << std::endl;
    stream << "    fi" << std::endl;
    stream << "    tmpIndex++;" << std::endl;
    stream << "  }" << std::endl;
    stream << "  :: else -> break;" << std::endl;
    stream << "  od" << std::endl;
    stream << "}" << std::endl;
}


}
