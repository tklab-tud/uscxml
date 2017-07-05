/**
 *  @file
 *  @author     2017 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef BENCHMARK_H_532562
#define BENCHMARK_H_532562

#include <mutex>
#include <map>
#include <chrono>
#include <string>
#include <ostream>

#include "uscxml/Common.h"              // for USCXML_API

namespace uscxml {

class USCXML_API Benchmark {
public:
	Benchmark(const std::string& domain);
	~Benchmark();

	static std::ostream& report(std::ostream& stream);
protected:
	std::string domain;
	std::chrono::time_point<std::chrono::system_clock> started;

	static std::map<std::string, size_t> benchmarks;
	static std::mutex benchMutex;
};

}
#endif /* end of include guard: BENCHMARK_H_532562 */
