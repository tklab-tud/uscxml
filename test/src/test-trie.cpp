#include "uscxml/util/Trie.h"
#include <iostream>
#include <assert.h>

using namespace uscxml;

int main(int argc, char** argv) {
	{
		Trie trie;
		int nrTokens = 0;
		size_t offset = 0;
		std::string word = "this is to be tokenized";
		std::string token;
		while((offset = trie.getNextToken(word, offset, token)) != std::string::npos) {
			std::cout << "\"" << token << "\" ";
			nrTokens++;
		}
		std::cout << std::endl;
		assert(nrTokens == word.length());
	}

	{
		Trie trie(" ");
		int nrTokens = 0;
		size_t offset = 0;
		std::string word = "this is to be tokenized";
		std::string token;
		while(offset = trie.getNextToken(word, offset, token), token.length() > 0) {
			std::cout << "\"" << token << "\" ";
			nrTokens++;
		}
		std::cout << std::endl;
		assert(nrTokens == 5);
	}

	{
		Trie trie("#");
		int nrTokens = 0;
		size_t offset = 0;
		std::string word = "#bb#bbbb#b#bbb#bb#b#";
		std::string token;
		while(offset = trie.getNextToken(word, offset, token), token.length() > 0) {
			std::cout << "\"" << token << "\" ";
			nrTokens++;
		}
		std::cout << std::endl;
		assert(nrTokens == 6);
	}

	{
		Trie trie("  ");
		int nrTokens = 0;
		size_t offset = 0;
		std::string word = "  this is  to  be tokenized";
		std::string token;
		while(offset = trie.getNextToken(word, offset, token), token.length() > 0) {
			std::cout << "\"" << token << "\" ";
			nrTokens++;
		}
		std::cout << std::endl;
		assert(nrTokens == 3);
	}

	{
		Trie trie("");
		trie.addWord("a");
		trie.addWord("b");

		trie.dump();
	}

	{
		Trie trie(".");
		trie.addWord("foo.bar");
		trie.addWord("foo.foo");
		trie.addWord("foo.foo.baz");
		trie.addWord("foz.foo.baz");
		trie.addWord("foz.foo");

		trie.dump();

		std::list<TrieNode*> childs;

		childs = trie.getChildsWithWords(trie.root);
		assert(childs.size() == 5);

		assert(trie.getNodeWithPrefix("") == trie.root);

		childs = trie.getWordsWithPrefix("");
		assert(childs.size() == 5);
	}
}