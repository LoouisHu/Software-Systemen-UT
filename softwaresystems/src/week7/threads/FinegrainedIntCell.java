package week7.threads;

import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class FinegrainedIntCell implements IntCell {
	final Lock lock = new ReentrantLock();
	final Condition isFull = lock.newCondition();
	final Condition isEmpty = lock.newCondition();
	private int value = 0;
	private boolean hasValue = false;

	@Override
	public void setValue(int val) {
		lock.lock();
		while (hasValue) {
			try {
				isEmpty.await();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		value = val;
		hasValue = true;
		isFull.signal();
		lock.unlock();

	}

	@Override
	public int getValue() {
		lock.lock();
		int result = -1;
		while (!hasValue) {
			try {
				isFull.await();

			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		result = value;
		hasValue = false;
		isEmpty.signal();
		lock.unlock();
		return result;
	}

}
