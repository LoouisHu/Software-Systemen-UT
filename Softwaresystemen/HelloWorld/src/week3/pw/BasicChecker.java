package week3.pw;

import ss.week1.Password;

public class BasicChecker implements Checker {

	@Override
	public boolean acceptable(String check) {
		// TODO Auto-generated method stub
		return check.length() >= 6 && !check.contains(" ");
	}
	
	public String generatePassword(){
		return "password123";
	}
}
