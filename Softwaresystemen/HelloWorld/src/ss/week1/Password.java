package ss.week1;

public class Password {

	public static String INITIAL = "GERARD";
	public static int MIN_LENGTH = 6;
	public String password;

	public Password() {
		this.password = INITIAL;
	}
	
	public boolean acceptable(String suggestion){
		return (suggestion.length()>= MIN_LENGTH && !suggestion.contains(" "));
	}
	
	public boolean testWord (String test){
		return(test.equals(password));	
	}
	
	public boolean setWord(String oldpass, String newpass){
		if (testWord(oldpass) && acceptable(newpass)) {
			password = newpass;
			return true;
			
		}
		return false;
	}
}

