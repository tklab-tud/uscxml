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

#include "Benchmark.h"

namespace uscxml {

std::mutex Benchmark::benchMutex;
std::map<std::string, size_t> Benchmark::benchmarks;
    
Benchmark::Benchmark(const std::string& domain) : domain(domain), started(std::chrono::system_clock::now()) {
}

Benchmark::~Benchmark() {
    std::lock_guard<std::mutex> lock(benchMutex);
    benchmarks[domain] += std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::system_clock::now() - started).count();
}
 
std::ostream& Benchmark::report(std::ostream& stream) {
    std::lock_guard<std::mutex> lock(benchMutex);

    size_t longestDomain = 0;
    for (auto benchmark : benchmarks) {
        longestDomain = (benchmark.first.size() > longestDomain ? benchmark.first.size() : longestDomain);
    }
    longestDomain += 8;
    
    for (auto benchmark : benchmarks) {
        std::string padding;
        for (int i = benchmark.first.size(); i < (longestDomain - log10(benchmark.second)); i++) {
            padding += " ";
        }
        
        stream << benchmark.first << ":" << padding << (double)benchmark.second / 1000.0 << "ms" << std::endl;
    }
    return stream;
}

}
