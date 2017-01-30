/**
 *  @file
 *  @author     2012-2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef TRIE_H_UZMQRBO5
#define TRIE_H_UZMQRBO5

#include "uscxml/Common.h"
#include <string>
#include <map>
#include <list>

namespace uscxml {

struct USCXML_API TrieNode {
	TrieNode();
	virtual ~TrieNode();

	bool hasWord;
	int index;
	std::string identifier;
	std::string value;
	std::map<std::string, TrieNode*> childs;
//	void dump(size_t indent = 0);
};

struct USCXML_API Trie {
	Trie();
	Trie(const std::string& seperator);
	virtual ~Trie();

	void addWord(const std::string& word);
	size_t getNextToken(const std::string& word, size_t offset, std::string& token);
	std::string escapeWord(const std::string& word);

	TrieNode* getNodeWithPrefix(const std::string& prefix);
	std::list<TrieNode*> getWordsWithPrefix(const std::string& prefix);
	std::list<TrieNode*> getChildsWithWords(TrieNode* node);
//	void dump();

	TrieNode* root;
	std::string seperator;
	int lastIndex;
};

}


#endif /* end of include guard: TRIE_H_UZMQRBO5 */
