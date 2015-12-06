package ss.week2.hotel;

public class Safe {
	//private invariant password != null;
	private Password password = new Password();
	private boolean activate;
	private boolean open;
	
	//@private invariant activate == true;
	//@private invariant activate == false;
	//@private invariant open == true;
	//@private invariant open == false;
	
	public Safe(){
		activate = false;
		open = false;
	}
	
//ensures isActive*( == true;
	public void activate(String pass){
		if (password.testWord(pass)){ 
			this.activate = true;
		}
	}
	
	//@ensures isActive() == false;
	//@ensures isOpen() == false;
	public void deactivate(){
		this.activate = false;
		
		assert (this.activate == false);
	}
	
	//@requires isActive() == true;
	//@ ensures getPassword().testWord(pass) ==> isOpen() == true;
	//@ensures \old(isOpen()) == true ==> isOpen();
	public void open(String pass){
		if (password.testWord(pass)){
			this.open = true;
		}
	}
	
	//@ensures isOpen() == false;
	public void close(){
		this.open = false;
		
		assert (this.open == false);
	}
	
	/*pure*/public boolean isActive(){
		return activate;
	}
	
	/*pure*/public boolean isOpen(){
		return open;
	}
	
	/*pure*/public Password getPassword(){
		return password;
	}
	
	public void setNullPass(){
		password = null;
	}
	
	public static void main(String[] args){

	}
}
