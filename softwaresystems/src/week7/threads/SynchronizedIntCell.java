package week7.threads;

public class SynchronizedIntCell implements IntCell {
	private int value = 0;

	public synchronized void setValue(int valueArg) {
		while (value != 0) {
			try {
				this.notify();
				this.wait();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		value = valueArg;
		this.notify();
	}

	public synchronized int getValue() {
		while (value == 0) {
			try {
				this.notify();
				this.wait();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		int oldval = value;
		value = 0;
		this.notify();
		return oldval;
	}
}

