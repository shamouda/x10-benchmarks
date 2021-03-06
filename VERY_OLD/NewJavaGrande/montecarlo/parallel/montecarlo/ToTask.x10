/*
 *
 * (C) Copyright IBM Corporation 2006
 *
 *  This file is part of X10 Test.
 *
 */
package montecarlo.parallel.montecarlo;

/**
 * X10 port of montecarlo benchmark from Section 2 of Java Grande Forum Benchmark Suite (Version 2.0).
 *
 * @author Vivek Sarkar (vsarkar@us.ibm.com)
 *
 * Porting issues identified:
 * 1) Remove Java package structure
 * 2) Add declaration to extend x10.lang.Object
 */
public class ToTask {//implements java.io.Serializable {
	private var header: String;
	private var randomSeed: long;

	public def this(var header: String, var randomSeed: long): ToTask = {
		this.header         = header;
		this.randomSeed     = randomSeed;
	}

	//------------------------------------------------------------------------
	// Accessor methods for class ToTask.
	// Generated by 'makeJavaAccessor.pl' script.  HWY.  20th January 1999.
	//------------------------------------------------------------------------

	/**
	 * Accessor method for private instance variable <code>header</code>.
	 * @return Value of instance variable <code>header</code>.
	 */
	public def get_header(): String = {
		return (this.header);
	}

	/**
	 * Set method for private instance variable <code>header</code>.
	 * @param header the value to set for the instance variable <code>header</code>.
	 */
	public def set_header(var header: String): void = {
		this.header = header;
	}

	/**
	 * Accessor method for private instance variable <code>randomSeed</code>.
	 * @return Value of instance variable <code>randomSeed</code>.
	 */
	public def get_randomSeed(): long = {
		return (this.randomSeed);
	}

	/**
	 * Set method for private instance variable <code>randomSeed</code>.
	 * @param randomSeed the value to set for the instance variable <code>randomSeed</code>.
	 */
	public def set_randomSeed(var randomSeed: long): void = {
		this.randomSeed = randomSeed;
	}

	//------------------------------------------------------------------------
}
