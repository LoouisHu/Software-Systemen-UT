package week7.account;

public class AccountSync {

	public static void main(String[] args){
		Account account = new Account();
		Thread t1 = new MyThread(100, 200, account);
		Thread t2 = new MyThread(-100,200, account);
		
		t1.start();
		t2.start();
		
		try{
			t1.join();
			t2.join();
		} catch (InterruptedException e){
			e.printStackTrace();
		}
		
		System.out.println(account.getBalance());
	}
	
}
