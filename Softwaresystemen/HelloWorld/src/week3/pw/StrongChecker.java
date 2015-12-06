package week3.pw;

public class StrongChecker extends BasicChecker {

	@Override
	public boolean acceptable(String check) {
		// TODO Auto-generated method stub
		return super.acceptable(check) && Character.isLetter(check.charAt(0)) && Character.isDigit(check.charAt(check.length()-1));
	}
	public String generatePassword(){
		return "password123";
		
	}

}
