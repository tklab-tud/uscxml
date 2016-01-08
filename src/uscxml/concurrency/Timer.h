// Copyright 2013 Alex Reece.
//
// A cross platform monotonic timer.

// see https://github.com/awreece/monotonic_timer

#ifndef MONOTONIC_TIMER_H_
#define MONOTONIC_TIMER_H_

// Returns seconds since some unspecified start time (guaranteed to be
// monotonicly increasing).

// Copyright 2015 Stefan Radomski.

namespace uscxml {

class USCXML_API Timer {
public:
    
    static double monotonic_seconds();

    Timer() {
        invocations = 0;
        elapsed = 0;
    }
    
    void start() {
        if (invocations == 0) {
            started = monotonic_seconds();
        }
        invocations++;
    }

    void stop() {
        if (invocations == 0)
            return;
        
        invocations--;
        if (invocations == 0) {
            elapsed += monotonic_seconds() - started;
        }
    }

    ~Timer() {
    }
    double elapsed;

protected:
    size_t invocations;
    double started;
};
    
class USCXML_API Measurement {
public:
    Measurement(Timer* timer) : timer(timer) {
        timer->start();
    }

    ~Measurement() {
        timer->stop();
    }

protected:
    Timer* timer;
};

}
#endif  // MONOTONIC_TIMER_H_
