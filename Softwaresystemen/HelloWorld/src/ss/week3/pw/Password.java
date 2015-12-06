package ss.week3.pw;

public class Password {

	public static final String INITIAL = "GERARDORER";
	public static int MIN_LENGTH = 6;
	public String password;
	public Checker checker;
	public String factoryPassword;

	public Password(Checker checker) {
		this.checker = checker;
		factoryPassword = checker.generatePassword();
		password = factoryPassword;
	}
	
	public Password(){
		this(new BasicChecker());
	}
	
	public Checker getChecker(){
		return checker;
	}
	
	public boolean acceptable(String suggestion){
		return (checker.acceptable(suggestion));
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

