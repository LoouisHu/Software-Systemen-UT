package ss.week3.pw;	

public class TimedPassword extends Password {
	private boolean isExpired = false;
	private long validTime = 0;
	private long startTime = 0;
	
	public TimedPassword() {
		validTime = 30000;
		startTime = System.currentTimeMillis();
	}
	
	public TimedPassword(int value){
		startTime = System.currentTimeMillis();
		validTime = (value * 30000 );
	
		
	}
	
	public boolean isExpired(){
		return !((System.currentTimeMillis()-startTime) <= validTime);
	}
	
	public boolean setWord(String oldpass, String newpass){
		if (super.setWord(oldpass , newpass)){
			startTime = System.currentTimeMillis();		
		}return false;
	}
	//public static void main(String[] args){
		//System.out.println(System.currentTimeMillis());
	//}

}
