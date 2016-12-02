package org.uscxml;

/**
 * @author sradomski
 *
 * This is the base class inheriting the abstract StateChart class
 * It is supposed to realize the callbacks with the language features
 * found in Java5 only.
 */

public class StateChartJava5Impl extends StateChart {
	
	DataModel dataModel;
	
	@Override
	public boolean isTrue(String expression) {
		return dataModel.evalAsBool(expression);
	}

	@Override
	public void raiseDoneEvent(State state, DoneData doneData) {
		// TODO Auto-generated method stub
	}

	@Override
	public void execContentLog(String label, String expression) {
		// TODO Auto-generated method stub
	}

	@Override
	public void execContentRaise(String event) {
		// TODO Auto-generated method stub

	}

	@Override
	public void execContentSend(Send send) {
		// TODO Auto-generated method stub

	}

	@Override
	public void execContentForeachInit(Foreach foreach) {
		// TODO Auto-generated method stub

	}

	@Override
	public void execContentForeachNext(Foreach foreach) {
		// TODO Auto-generated method stub

	}

	@Override
	public void execContentForeachDone(Foreach foreach) {
		// TODO Auto-generated method stub

	}

	@Override
	public void execContentAssign(Assign assign) {
		// TODO Auto-generated method stub

	}

	@Override
	public void execContentInit(Data data) {
		// TODO Auto-generated method stub

	}

	@Override
	public void execContentCancel(String sendId, String sendIdExpr) {
		// TODO Auto-generated method stub

	}

	@Override
	public void execContentScript(String src, String content) {
		// TODO Auto-generated method stub

	}

	@Override
	public void execContentFinalize(Invoke invoker, Object event) {
		// TODO Auto-generated method stub

	}

}
