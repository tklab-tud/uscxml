package org.uscxml.tests.gen;

import org.uscxml.InterpreterException;
import org.uscxml.gen.StateChart;
import org.uscxml.gen.TestStateChartBase;

public class TestStateChart extends TestStateChartBase {

	@Override
	public void execContentLog() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void execContentRaise() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void execContentSend() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void execContentForeachInit() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void execContentForeachNext() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void execContentForeachDone() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void execContentAssign() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void execContentInit() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void execContentCancel() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void execContentScript() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void invoke() {
		// TODO Auto-generated method stub
		
	}

	public static void main(String[] args) {
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
