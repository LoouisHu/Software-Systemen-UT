package week7.threads;

public class SynchronizedIntCell implements IntCell {
	private int value = 0;
	private boolean valueSet = false;
	
	public synchronized void setValue(int valueArg) {
		while (valueSet) {
			try {
				this.wait();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		value = valueArg;
		valueSet = true;
		this.notifyAll();
	}

	public synchronized int getValue() {
		while (!valueSet) {
			try {
				this.wait();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		int oldval = value;
		valueSet = false;
		this.notifyAll();
		return oldval;
	}
}

