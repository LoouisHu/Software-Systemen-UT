package week7.account;

public class MyThread extends Thread{
	double theAmount;
	int theFrequency;
	Account theAccount;
	
	public MyThread(double amount, int frequency, Account account){
		this.theAmount = amount;
		this.theFrequency = frequency;
		this.theAccount = account;
	}
	
	@Override
	public void run(){
		for (int i = 0; i < theFrequency; i++){
			theAccount.transaction(theAmount);
		}
	}	
	
	
}
