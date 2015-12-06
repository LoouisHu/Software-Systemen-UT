package ss.week1.hotel;

public class Guest {
	//Instance variables
	private String guest;
	private int number;
	private boolean in;
	private boolean out;
	private Room room;
	
	public Guest(String name){
		guest = name;
	}
	
	public String getName(){
		return guest;
	
	}
	
	public Room getRoom(){
		return room;
		}

	public boolean checkin(Room r){
		if (r.getGuest() == null){
			r.setGuest(this);
			room = r;
			return true;
		}
		else {
			return false;
		}
	}
	
	public boolean checkout(){
		if (this.getRoom
				() != null){
			room.setGuest(null);
			room = null;
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
