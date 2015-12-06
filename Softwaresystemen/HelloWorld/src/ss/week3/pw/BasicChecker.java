package ss.week3.pw;

public class BasicChecker implements Checker {
	
	public static final String INITPASS = Password.INITIAL;
	
	@Override
	public boolean acceptable(String check) {
		return check.length() >= 6 && !check.contains(" ");
	}
	
	public String generatePassword(){
		return "password";
		
	}

}
