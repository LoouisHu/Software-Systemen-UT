package week7.account;

import java.util.concurrent.locks.*;

public class Account {
	protected double balance = 0.0;
	final static Lock lock = new ReentrantLock();
	final Condition enoughBalance = lock.newCondition();

	public void transaction(double amount) {
		lock.lock();
		try{
			while(balance + amount <= -1000){
				enoughBalance.await();
			}
		balance = balance + amount;
		enoughBalance.signal();
		} catch (InterruptedException e) {
			e.printStackTrace();
		} finally {
			lock.unlock();
		}
	}
	public double getBalance() {
		return balance;

	}
}
