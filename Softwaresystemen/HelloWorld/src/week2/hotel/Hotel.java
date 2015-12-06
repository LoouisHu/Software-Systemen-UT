package week2.hotel;

public class Hotel {

	private Room kamer1;
	private Room kamer2;
	private Guest henk;
	private Guest karel;
	private Password access;
	private String hotelname;
	
	//@requires name != null;
	//@ensures getHotelname().equals(name);
	//@ensures getPassword().testWord(Password.INITIAL);
	
	/*@ pure */ public Hotel(String name){
		hotelname = name;
		kamer1 = new Room(1);
		kamer2 = new Room(2);
		access = new Password();
	}
	
	//@requires guestname != null;
	//@requires checkinPassword != null;
	
	public Room checkIn(String checkinPassword, String guestname){
		
		assert(guestname != null);
		assert(checkinPassword != null);
		if(access.getPassword().equals(checkinPassword)){
			if (kamer1.getGuest() == null){
				henk = new Guest(guestname);
				henk.checkin(kamer1);
				return kamer1;
			}
				
			else if(kamer2.getGuest() == null){
				karel = new Guest(guestname);
				karel.checkin(kamer2);
				return kamer2;
			}
			}
		return null;
}

	//@requires guestname != null;
	
	public void checkOut(String guestname){
		if (kamer1.getGuest() != null && kamer1.getGuest().getName().equals(guestname)){
			henk.checkout();
			kamer1.getSafe().deactivate();
			return;
		}
		else if(kamer2.getGuest() != null && kamer2.getGuest().getName().equals(guestname)){
			karel.checkout();
			kamer2.getSafe().deactivate();
			return;
		}
	
	}
	
	//@ensures \result == null;
	/*@ pure */ public Room getFreeRoom(){
		if(kamer1.getGuest() == null){
			return kamer1;
		}
		else if(kamer2.getGuest() == null){
			return kamer2;
		}
		else{
			return null;
			
		}
	}
	
	//@requires guestname != null;
	
	/*@ pure */ public Room getRoom(String guestname){
		if(kamer1.getGuest() != null){
			if(kamer1.getGuest().getName().equals(guestname)){
				return kamer1;
			}
			else{
				return null;
			}
		}
		return null;
	}
	//@ ensures \result != null;
		/*@ pure */ public Password getPassword(){
			return access;
		}
		
		public String toString(){
			if(kamer1.getGuest() != null){
				return kamer1.getGuest().getName();
			}
			else{
				return null;
			}
		}
		
		//@ensures \result != null;
		/*@ pure */public String getHotelname(){
			return this.hotelname;
		}
}	