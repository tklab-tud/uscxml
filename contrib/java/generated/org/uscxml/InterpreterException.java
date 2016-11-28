package org.uscxml;

public class InterpreterException extends Exception {
	private static final long serialVersionUID = -3534919496547591015L;
	
	public InterpreterException(String name, String msg) {
		super(msg);
	}
	
	public String name;
}
