package week7;

import java.util.concurrent.locks.*;

//7.21 1. De string text wordt aangepast dus die is critical (degene in de run);
//	   2. "one;two" "two;one;", komt omdat er een start() wordt geïnitialiseerd op beide ConcatThreads op text
//		  ze kunnen beiden "" lezen en dan one; of two; schrijven en dan heb je alleen one of two.
//		  dus 
public class ConcatThread extends Thread {
	private static String text = ""; // global variable
	private String toe;
	private static Object monitor = new Object();
	private final Lock lock = new ReentrantLock();
	private final Condition isTwo = lock.newCondition();

	public ConcatThread(String toeArg) {
		this.toe = toeArg;
	}

	public void run() {
		synchronized (monitor) {
			try {
				if (toe.equals("") && toe.equals("two;"))
					monitor.wait();
				
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
			text = text.concat(toe);
			monitor.notify();
		}

	}

	public static void main(String[] args) {
		(new ConcatThread("one;")).start();
		(new ConcatThread("two;")).start();
	}
}
