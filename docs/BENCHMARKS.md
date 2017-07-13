# Benchmarks

We did conceive a [series of benchmark](https://github.com/tklab-tud/uscxml/tree/master/test/benchmarks) SCXML documents to evaluate the performance of the various SCXML implementations. The state-charts in the benchmarks are completely artificial and bear no resemblance to real-world state-charts. However, they may provide a general guidance to get an impression about the performance of the different implementations.

The state-charts each stress a specific feature of any SCXML `microstep(T)` implementation. Each contains a state `mark` that is continuously entered and exited as part of a sequence of spontaneous microsteps and measures the entries per second. For every implementation, the [benchmark is run](https://github.com/tklab-tud/uscxml/blob/master/contrib/benchmarks/run.sh) for a number of seconds and the iterations per seconds are averaged. The benchmarks exist in increasing complexity from very simple with, e.g., 4 states nested in a depth of 4 compounds up until 512 for state-charts with > 250.000 states.

**Note:** If you are the author / maintainer of one of the SCXML implementations being benchmarked below and feel that I misrepresent your implementation's performance, post an issue and I will set things straight.

**Note:** There are two `microstep(T)` implementations in uSCXML, namely `fast` and `large` with the former being the default for transpilation and the latter for interpretation. Both are being employed on an interpreted state-chart here. For the `fast` microstep implementation we measured the case with pre-calculated predicates.

**Note:** The numbers for scxmlcc are necessarily for the compiled case and N/A if we could not compile the state-chart within the time limit.

## Transitions

The Transitions benchmark measures transition selection with many conflicting transitions enabled as part of a microstep.

![Transition Benchmark](https://user-images.githubusercontent.com/980655/27858834-004c9c78-6177-11e7-8519-2f73f0ff9fb4.png)

## LCCA
When exiting a state via a transition, the least-common compound ancestor (LCCA) of the transition's targets and source state has to be identified. This is a common operation and its runtime is proportional to the nesting depth if implemented respectively.

![LCCA Benchmark](https://user-images.githubusercontent.com/980655/27858835-00527ecc-6177-11e7-85d2-46c83ad5ed71.png)

## Conclusion

uSCXML with either microstep implementation is consistently the fastest with the exception of the Transitions benchmark, where the compiled `scxmlcc` is degenerating slower for more complex state-charts. This may be due to compiler optimizations (or an incomplete implementation) and it would be interesting to compare `scxmlcc` against the transpiled ANSI-C code from `uscxml-transform`. However, the limiting factor here becomes the time required to transpile the state-chart or to compile the generated source file into an executable binary respectively. With regard to huge state-charts, the large microstep implementation of `uSCXML` performs best and retains acceptable performance throughout the range of benchmarks, only surpassed by the fast implementation for smaller complexities.
