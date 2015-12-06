package week2.hotel;

import ss.week1.Password;

public class Safe {
	private Password password;
	private boolean activate;
	private boolean open;
	public Safe(){
		password = new Password();
		
	}
		
	public void activate(String pass){
		if (password.testWord(pass)){
				this.activate = true;
			}
	}
	
	public void deactivate(){
		this.activate = false;
			
		assert (this.activate == false);
		
	}
	
	public void open(String pass){
		if(password.testWord(pass)){
			this.open = true;
		}
	}
	
	public void close(){
		this.open = false;
		
		assert (this.open == false);

	}

	public boolean isActive(){
		return activate;
	}
	
	public boolean isOpen(){
		return open;
	}
	
	
	public Password getPassword() { 
	 	return password; 
	 	} 
	 	 
	 public void setNullPassword() { 
	 		password = null; 
	 	} 

	public static void main(String[] args){
		Safe henk = new Safe();
		henk.setNullPassword();
		henk.getPassword();
		System.out.println("test");
		
		
		
	}
}
