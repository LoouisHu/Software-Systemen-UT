package week2.hotel;

public class Guest {
	//Instance variables
	private String guest;
	//private int number;
	//private boolean in;
	//private boolean out;
	private Room kamer;
	
	public Guest(String name){
		guest = name;
	}
	
	public String getName(){
		return guest;
	
	}
	
	public Room getRoom(){
		return kamer;
		}

	public boolean checkin(Room k){
		if (k.getGuest() == null){
			k.setGuest(this);
			kamer = k;
			return true;
		}
		else {
			return false;
		}
	}
	
	public boolean checkout(){
		if (this.getRoom
				() != null){
			kamer.setGuest(null);
			kamer = null;
		return true;
		}
		
		else{
			return false;
		}
	
	}
	public String toString(){
		return "Name of guest: " + guest;
		
	}
}
