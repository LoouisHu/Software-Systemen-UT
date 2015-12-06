package ss.week3.pw;

public interface Checker {
	/*@pure
	 * requires check != null;
	 * requires check.length() <= 16;
	 * 
	 */
	boolean acceptable(String check);
	
	}
