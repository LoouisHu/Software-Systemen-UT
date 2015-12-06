package ss.week2.hotel;

/**
 * Returns guest names and room number, whether they are checked in or not.
 * 
 * @author Louis
 * @version 0.0.1a
 * @param guest
 * @param number
 * @returns Guest name and room number
 * @see Guest
 */

public class Guest{
	
	// Instance variables
	
	private String guest;
	private Room room;
	
	//Constructor
	
	public Guest(String name){
		guest = name;
	}
	
	//Methods
	
	public String getName(){
		return guest;
	}
	
	public Room getRoom(){
		return room;
	}
	
	public boolean checkin(Room r){
		if(r.getGuest() == null){
		r.setGuest(this);
		room = r;
		return true;
		}
		else{
			return false;
			}
		}
	

	public boolean checkout(){
		if (this.getRoom() != null){
			room.setGuest(null);
			room = null;
		return true;
	}
		else{
		return false;
	}
	}
	
	public String toString(){
		return "Name of guest: " + getName();
	}
}