package org.uscxml.benchmark;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import java.net.URL;
import java.util.List;

import org.apache.commons.scxml2.*;

import org.apache.commons.scxml2.env.SimpleDispatcher;
import org.apache.commons.scxml2.env.SimpleErrorReporter;
import org.apache.commons.scxml2.env.Tracer;
import org.apache.commons.scxml2.io.SCXMLReader;
import org.apache.commons.scxml2.io.SCXMLReader.Configuration;
import org.apache.commons.scxml2.model.CustomAction;
import org.apache.commons.scxml2.model.EnterableState;
import org.apache.commons.scxml2.model.Transition;
import org.apache.commons.scxml2.model.SCXML;
import org.apache.commons.scxml2.model.TransitionTarget;
import org.apache.commons.scxml2.model.EnterableState;
import org.apache.commons.scxml2.model.TransitionTarget;

/**
 * Unit test for simple App.
 */
public class BenchmarkTest extends TestCase {

    public long initMs = 0;

    class PerformanceListener extends SimpleErrorReporter implements SCXMLListener {
        public long iterations = 0;
        public long mark = System.currentTimeMillis();

        public void onEntry(final EnterableState state) {
            if (state.getId().equals("mark")) {
                iterations++;
                long now = System.currentTimeMillis();
                if (now - mark > 1000) {
                    System.out.println(initMs + ", " + iterations);
                    mark = now;
                    iterations = 0;
                }
            }
        }
        public void onExit(final EnterableState state) {}
        public void onTransition(final TransitionTarget from, final TransitionTarget to, final Transition transition, String event) {}

    }

  public SCXML parse(final URL url, final List<CustomAction> customActions) throws Exception {
      Configuration configuration = new Configuration(null, null, customActions);
      SCXML scxml = SCXMLReader.read(url, configuration);
      return scxml;
  }

  public SCXMLExecutor getExecutor(final SCXML scxml, final Evaluator evaluator, final EventDispatcher eventDispatcher) throws Exception {
      PerformanceListener trc = new PerformanceListener();
      SCXMLExecutor exec = new SCXMLExecutor(evaluator, eventDispatcher, null);
      exec.setStateMachine(scxml);
      exec.addListener(scxml, trc);
      return exec;
  }

    /**
     * Create the test case
     *
     * @param testName name of the test case
     */
    public BenchmarkTest( String testName )
    {
        super( testName );
    }

    /**
     * @return the suite of tests being tested
     */
    public static Test suite()
    {
        return new TestSuite( BenchmarkTest.class );
    }

    /**
     * Rigourous Test :-)
     */
    public void testApp()
    {
        try {
            long started = System.currentTimeMillis();
            String fileName = System.getenv("USCXML_BENCHMARK");
            SCXML scxml = parse(new URL("file:" + fileName), null);
            SCXMLExecutor exec = getExecutor(scxml, null, new SimpleDispatcher());
            initMs = System.currentTimeMillis() - started;
            exec.go();
        } catch (Exception e) {
            System.err.println(e);
            assertTrue(false);
        }
    }
}
