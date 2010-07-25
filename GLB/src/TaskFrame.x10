/**
 * <p>
 * The state needed to run a task typically can be broken down into
 * state that is common across all tasks (e.g. parameters), and
 * state specific to the task. So we introduce the concept of a 
 * <code>Runner</code>. A Runner is associated with a particular
 * kind of task and typically contains the state that is common
 * across all tasks.
 *
 *<p>
 * Running a task may cause other tasks to be created. 
 * These tasks are pushed onto the given stack.
 * @author vj
 */

import x10.util.Stack;
/**
 * A TaskFrame provides additional parameters that may be necessary to
 * execute a task. Typically, there is one TaskFrame instance per place.
 */
public interface TaskFrame[T] {
	/**
	 * Run this task in the given task frame. 
	 * Implementations of this method will use 
	 * the stack to create additional tasks, if necessary.
	 */
	def runTask(t:T, stack:Stack[T]!):Void;
	
	/**
	 * Run this task as a root task. Implementations of this method
	 * will use the stack to create additional tasks, if necessary.
	 */
	def runRootTask(t:T, stack:Stack[T]!):Void;
}