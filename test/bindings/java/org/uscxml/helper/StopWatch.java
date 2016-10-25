package org.uscxml.helper;

import org.uscxml.Data;
import org.uscxml.DataModelExtension;

public class StopWatch {

	public StopWatch() {
	}
	
	public void reset() {
		System.out.println("RESET");
	}
	
	public void start() {
		System.out.println("START");
	}
	public void stop() {
		System.out.println("STOP");
	}
	
}
