package org.uscxml.helper;

import org.uscxml.InterpreterMonitor;
import org.uscxml.StringList;

public class TestMonitor extends InterpreterMonitor {

	public TestMonitor() {}
	
	@Override
	public void beforeExitingState(String stateId, String xpath, String stateXML) {
		System.out.println("beforeExitingState: " + stateId + " " + xpath);
	}

	@Override
	public void afterExitingState(String stateId, String xpath, String stateXML) {
		System.out.println("afterExitingState: " + stateId + " " + xpath);
	}

	@Override
	public void beforeExecutingContent(String tagName, String xpath, String contentXML) {
		System.out.println("afterExecutingContent: " + tagName + " " + xpath);
	}

	@Override
	public void afterExecutingContent(String tagName, String xpath, String contentXML) {
		System.out.println("afterExecutingContent: " + tagName + " " + xpath);
	}

	@Override
	public void beforeUninvoking(String xpath, String invokeid, String invokerXML) {
		System.out.println("beforeUninvoking: " + xpath + " " + invokeid);
	}

	@Override
	public void afterUninvoking(String xpath, String invokeid, String invokerXML) {
		System.out.println("beforeUninvoking: " + xpath + " " + invokeid);
	}

	@Override
	public void beforeTakingTransition(String xpath, String source, StringList targets, String transitionXML) {
		System.out.println("beforeTakingTransition: " + xpath + " " + source + " " + targets);
	}

	@Override
	public void afterTakingTransition(String xpath, String source, StringList targets, String transitionXML) {
		System.out.println("afterTakingTransition: " + xpath + " " + source + " " + targets);
	}

	@Override
	public void beforeEnteringState(String stateId, String xpath, String stateXML) {
		System.out.println("beforeEnteringState: " + stateId + " " + xpath);
	}

	@Override
	public void afterEnteringState(String stateId, String xpath, String stateXML) {
		System.out.println("afterEnteringState: " + stateId + " " + xpath);
	}

	@Override
	public void beforeInvoking(String xpath, String invokeid, String invokerXML) {
		System.out.println("beforeInvoking: " + xpath + " " + invokeid);
	}

	@Override
	public void afterInvoking(String xpath, String invokeid, String invokerXML) {
		System.out.println("afterInvoking: " + xpath + " " + invokeid);
	}

	
}
