package org.uscxml.tests.gen;

import org.uscxml.InterpreterException;
import org.uscxml.StateChart;
import org.uscxml.gen.TestStateChartBase;

public class TestStateChart extends TestStateChartBase {
	
	public static void main(String[] args) {
		System.out.println("Testing " + args[0]);
		
		TestStateChart machine = new TestStateChart();
		try {
			while(machine.step() != StateChart.InterpreterState.USCXML_FINISHED) {
				// here we could inspect the state chart after a step
			}
			// when we arrive here, the state chart is finished
			assert(machine.isInState("pass"));
			System.out.println("PASSED");
			System.exit(0); // EXIT_SUCCESS
		} catch (InterpreterException e) {
			System.out.println("FAILED");
			System.exit(-1); // EXIT_FAILURE
		}
	}

}
