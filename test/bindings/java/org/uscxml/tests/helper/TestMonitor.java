package org.uscxml.tests.helper;

import org.uscxml.InterpreterIssue;
import org.uscxml.InterpreterMonitor;
import org.uscxml.StringList;

public class TestMonitor extends InterpreterMonitor {

	public TestMonitor() {}
	
	@Override
	public void beforeExitingState(String stateId, String xpath, String stateXML) {
		System.out.println("beforeExitingState: " + stateId + " " + xpath + " " + stateXML);
	}

	@Override
	public void afterExitingState(String stateId, String xpath, String stateXML) {
		System.out.println("afterExitingState: " + stateId + " " + xpath + " " + stateXML);
	}

	@Override
	public void beforeExecutingContent(String tagName, String xpath, String contentXML) {
		System.out.println("afterExecutingContent: " + tagName + " " + xpath + " " + contentXML);
	}

	@Override
	public void afterExecutingContent(String tagName, String xpath, String contentXML) {
		System.out.println("afterExecutingContent: " + tagName + " " + xpath + " " + contentXML);
	}

	@Override
	public void beforeUninvoking(String xpath, String invokeid, String invokerXML) {
		System.out.println("beforeUninvoking: " + xpath + " " + invokeid + " " + invokerXML);
	}

	@Override
	public void afterUninvoking(String xpath, String invokeid, String invokerXML) {
		System.out.println("beforeUninvoking: " + xpath + " " + invokeid + " " + invokerXML);
	}

	@Override
	public void beforeTakingTransition(String xpath, String source, StringList targets, String transitionXML) {
		System.out.println("beforeTakingTransition: " + xpath + " " + source + " " + targets + " " + transitionXML);
	}

	@Override
	public void afterTakingTransition(String xpath, String source, StringList targets, String transitionXML) {
		System.out.println("afterTakingTransition: " + xpath + " " + source + " " + targets + " " + transitionXML);
	}

	@Override
	public void beforeEnteringState(String stateId, String xpath, String stateXML) {
		System.out.println("beforeEnteringState: " + stateId + " " + xpath + " " + stateXML);
	}

	@Override
	public void afterEnteringState(String stateId, String xpath, String stateXML) {
		System.out.println("afterEnteringState: " + stateId + " " + xpath + " " + stateXML);
	}

	@Override
	public void beforeInvoking(String xpath, String invokeid, String invokerXML) {
		System.out.println("beforeInvoking: " + xpath + " " + invokeid + " " + invokerXML);
	}

	@Override
	public void afterInvoking(String xpath, String invokeid, String invokerXML) {
		System.out.println("afterInvoking: " + xpath + " " + invokeid + " " + invokerXML);
	}

	@Override
	public void reportIssue(InterpreterIssue issue) {
		System.out.println(issue);
	}
	
}
