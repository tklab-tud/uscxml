// Copyright 2013 Alex Reece.
//
// A cross platform monotonic timer.

// see https://github.com/awreece/monotonic_timer

#include "uscxml/config.h"
#ifdef HAS_UNISTD_H
#include <unistd.h>
#endif
#include "Timer.h"

#define NANOS_PER_SECF 1000000000.0
#define USECS_PER_SEC 1000000

#if _POSIX_TIMERS > 0 && defined(_POSIX_MONOTONIC_CLOCK)
  // If we have it, use clock_gettime and CLOCK_MONOTONIC.

  #include <time.h>

  double uscxml::Timer::monotonic_seconds() {
    struct timespec time;
    // Note: Make sure to link with -lrt to define clock_gettime.
    clock_gettime(CLOCK_MONOTONIC, &time);
    return ((double) time.tv_sec) + ((double) time.tv_nsec / (NANOS_PER_SECF));
  }

#elif defined(__APPLE__)
  // If we don't have CLOCK_MONOTONIC, we might be on a Mac. There we instead
  // use mach_absolute_time().

  #include <mach/mach_time.h>

  static mach_timebase_info_data_t info;
  static void __attribute__((constructor)) init_info() {
    mach_timebase_info(&info);
  }

  double uscxml::Timer::monotonic_seconds() {
    uint64_t time = mach_absolute_time();
    double dtime = (double) time;
    dtime *= (double) info.numer;
    dtime /= (double) info.denom;
    return dtime / NANOS_PER_SECF;
  }

#elif defined(_MSC_VER)
  // On Windows, use QueryPerformanceCounter and QueryPerformanceFrequency.

#define NOMINMAX
  #include <windows.h>

  static double PCFreq = 0.0;
__int64 CounterStart = 0;

  double uscxml::Timer::monotonic_seconds() {
    if (CounterStart == 0) {
      // Accoring to http://stackoverflow.com/a/1739265/447288, this will
      // properly initialize the QueryPerformanceCounter.

      LARGE_INTEGER li;
      int has_qpc = QueryPerformanceFrequency(&li);

      PCFreq = ((double) li.QuadPart) / 1000.0;
    }
    LARGE_INTEGER li;
    QueryPerformanceCounter(&li);
    return double(li.QuadPart - CounterStart)/PCFreq;
  }

#else
  // Fall back to rdtsc. The reason we don't use clock() is this scary message
  // from the man page:
  //     "On several other implementations, the value returned by clock() also
  //      includes the times of any children whose status has been collected via
  //      wait(2) (or another wait-type call)."
  //
  // Also, clock() only has microsecond accuracy.
  //
  // This whitepaper offered excellent advice on how to use rdtscp for
  // profiling: http://download.intel.com/embedded/software/IA/324264.pdf
  //
  // Unfortunately, we can't follow its advice exactly with our semantics,
  // so we're just going to use rdtscp with cpuid.
  //
  // Note that rdtscp will only be available on new processors.

  #include <stdint.h>

  static inline uint64_t rdtsc() {
    uint32_t hi, lo;
    asm volatile("rdtscp\n"
                 "movl %%edx, %0\n"
                 "movl %%eax, %1\n"
                 "cpuid"
                 : "=r" (hi), "=r" (lo) : : "%rax", "%rbx", "%rcx", "%rdx");
    return (((uint64_t)hi) << 32) | (uint64_t)lo;
  }

  static uint64_t rdtsc_per_sec = 0;
  static void __attribute__((constructor)) init_rdtsc_per_sec() {
    uint64_t before, after;

    before = rdtsc();
    usleep(USECS_PER_SEC);
    after = rdtsc();

    rdtsc_per_sec = after - before;
  }

  double uscxml::Timer::monotonic_seconds() {
    return (double) rdtsc() / (double) rdtsc_per_sec;
  }

#endif