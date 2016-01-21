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
		try {
			while (hasValue) {
				isEmpty.await();
			}
			value = val;
			hasValue = true;
			isFull.signal();
		} catch (InterruptedException e){
			e.printStackTrace();
		} finally {
			lock.unlock();
		}
		
	}

	@Override
	public int getValue() {
		lock.lock();
		int result = -1;
		try {
			while (!hasValue){
				isFull.await();
			}
			result = value;
			hasValue = false;
			isEmpty.signal();
			
		} catch (InterruptedException e){
			e.printStackTrace();
		} finally {
			lock.unlock();
		}
		return result;
	}

}
