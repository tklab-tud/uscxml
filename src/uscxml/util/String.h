/**
 *  @file
 *  @author     2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef STRING_H_FD462039
#define STRING_H_FD462039

#include <string>
#include <list>

namespace uscxml {

std::string escapeMacro(std::string const &s);

std::string toBinStr(size_t val, size_t margin);

std::list<std::string> tokenize(const std::string &line, const char seperator = ' ', bool trimWhiteSpace = true);

std::string spaceNormalize(const std::string &text);

bool nameMatch(const std::string &eventDescs, const std::string &event);

}

#endif /* end of include guard: STRING_H_FD462039 */
