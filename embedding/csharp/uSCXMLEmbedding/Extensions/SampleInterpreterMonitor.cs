using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using org.uscxml;

namespace embedding
{
    class SampleInterpreterMonitor : InterpreterMonitor
    {
        public override void afterCompletion(Interpreter interpreter) { }
        public override void afterMicroStep(Interpreter interpreter) { }
        public override void beforeCompletion(Interpreter interpreter) { }
        public override void beforeMicroStep(Interpreter interpreter) { }
        public override void beforeProcessingEvent(Interpreter interpreter, Event arg1) { }
        public override void onStableConfiguration(Interpreter interpreter) { }
        public override void afterEnteringState(Interpreter interpreter, string stateId, string xpath, string state, bool moreComing) { }
        public override void afterExecutingContent(Interpreter interpreter, string tagName, string xpath, string element) { }
        public override void afterExitingState(Interpreter interpreter, string stateId, string xpath, string state, bool moreComing) { }
        public override void afterInvoking(Interpreter interpreter, string xpath, string invokeid, string element) { }
        public override void afterTakingTransition(Interpreter interpreter, string xpath, string source, StringList targets, string element, bool moreComing) { }
        public override void afterUninvoking(Interpreter interpreter, string xpath, string invokeid, string element) { }
        public override void beforeEnteringState(Interpreter interpreter, string stateId, string xpath, string state, bool moreComing) { }
        public override void beforeExecutingContent(Interpreter interpreter, string tagName, string xpath, string element) { }
        public override void beforeExitingState(Interpreter interpreter, string stateId, string xpath, string state, bool moreComing) { }
        public override void beforeInvoking(Interpreter interpreter, string xpath, string invokeid, string element) { }
        public override void beforeTakingTransition(Interpreter interpreter, string xpath, string source, StringList targets, string element, bool moreComing) { }
        public override void beforeUninvoking(Interpreter interpreter, string xpath, string invokeid, string element) { }

    }
}
