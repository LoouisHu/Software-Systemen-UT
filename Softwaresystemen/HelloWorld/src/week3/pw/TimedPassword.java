package week3.pw;

public class TimedPassword extends Password {
	
	private long validTime = 0;
	private long startTime = 0;
	
	public TimedPassword(){
		validTime = 50000;
		startTime = System.currentTimeMillis();
		
	}
	public TimedPassword(long valid){
		validTime = (valid * 1000);
		startTime = System.currentTimeMillis();
		
		
	}
		
	public boolean isExpired(){
		return !((System.currentTimeMillis()-startTime)<= validTime);
	}
	
	
	public boolean setWord(String oldpass, String newpass){
		boolean result = false;
		if (super.setWord(oldpass, newpass)){
			startTime = System.currentTimeMillis();
			result = true;
		
		}
		return result;
	}	
}


