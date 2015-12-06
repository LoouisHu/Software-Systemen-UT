package ss.week3.pw;

public class StrongChecker extends BasicChecker {

	@Override
	public boolean acceptable(String check) {
		return super.acceptable(check) && Character.isLetter(check.charAt(0)) && Character.isDigit(check.charAt(check.length()-1));
	}

	public String generatePassword(){
		return "LABC333";
	}
	
}
