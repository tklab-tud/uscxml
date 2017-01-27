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

#include "Trie.h"
#include <iostream>
#include <boost/algorithm/string.hpp>

namespace uscxml {

Trie::Trie() {
	root = new TrieNode();
	lastIndex = 0;
}

Trie::Trie(const std::string& seperator) : seperator(seperator) {
	root = new TrieNode();
	lastIndex = 0;
}

Trie::~Trie() {
	delete root;
}

TrieNode::TrieNode() : hasWord(false) {}

TrieNode::~TrieNode() {
	std::map<std::string, TrieNode*>::iterator childIter = childs.begin();
	while(childIter != childs.end()) {
		delete childIter->second;
		childIter++;
	}
}

size_t Trie::getNextToken(const std::string& word, size_t offset, std::string& token) {
	if (offset == std::string::npos || offset >= word.length()) {
		token = "";
		return std::string::npos;
	}
	if (seperator.size() > 0) {
		size_t sepPos = word.find(seperator, offset);
		if (sepPos == offset) // starts with a seperator
			return getNextToken(word, offset + seperator.length(), token);
		if (sepPos == std::string::npos) {
			token = word.substr(offset, word.length() - offset);
		} else {
			token = word.substr(offset, sepPos - offset);
			sepPos += seperator.length();
		}
		return sepPos;
	}
	token = word[offset];
	return offset + 1;
}

std::string Trie::escapeWord(const std::string& word) {
	std::string identifier = word;
	boost::replace_all(identifier, ".", "_");
	return identifier;
}

void Trie::addWord(const std::string& word) {
	TrieNode* currNode = root;

	std::string prefix;
	size_t offset = 0;

	for(;;) {
		offset = getNextToken(word, offset, prefix);

		if (prefix.size() > 0) {
			if (currNode->childs.find(prefix) == currNode->childs.end())
				currNode->childs[prefix] = new TrieNode();
			currNode = currNode->childs[prefix];
		}

		if (offset == std::string::npos)
			break;
	}
	if (!currNode->hasWord) {
		currNode->index = lastIndex++;
		currNode->value = word;
		currNode->identifier = escapeWord(word);
		currNode->hasWord = true;
	}
}

TrieNode* Trie::getNodeWithPrefix(const std::string& prefix) {
	std::string token;
	size_t offset = 0;

	TrieNode* currNode = root;

	for(;;) {
		offset = getNextToken(prefix, offset, token);
		if (currNode->childs.find(token) == currNode->childs.end()) {
			if (token.size() > 0)
				currNode = NULL;
			break;
		} else {
			currNode = currNode->childs[token];
		}
	}
	return currNode;
}

std::list<TrieNode*> Trie::getWordsWithPrefix(const std::string& prefix) {
	std::list<TrieNode*> nodes;
	TrieNode* prefixNode = getNodeWithPrefix(prefix);

	if (prefixNode) {
		nodes = getChildsWithWords(prefixNode);
	}

	return nodes;
}

std::list<TrieNode*> Trie::getChildsWithWords(TrieNode* node) {
	std::list<TrieNode*> nodes;
	if (node->hasWord) {
		nodes.push_back(node);
	}

	std::map<std::string, TrieNode*>::iterator childIter = node->childs.begin();
	while(childIter != node->childs.end()) {
		std::list<TrieNode*> otherChilds = getChildsWithWords(childIter->second);
		nodes.merge(otherChilds);
		childIter++;
	}

	return nodes;
}

void TrieNode::dump(size_t indent) {
	std::string padding;
	for (size_t i = 0; i < indent; i++) {
		padding += "  ";
	}

	std::map<std::string, TrieNode*>::iterator childIter = childs.begin();
	while(childIter != childs.end()) {
		std::cout << padding << childIter->first;
		if (childIter->second->hasWord) {
			std::cout << " (word)";
		}
		std::cout << std::endl;
		childIter->second->dump(indent + 1);
		childIter++;
	}
}

void Trie::dump() {
	if (root->hasWord)
		std::cout << "(word)" << std::endl;
	root->dump();
}

}
