package ss.week2.hotel;

public class Hotel {
	//@ private invariant name != null;
	/**
	 * variable name for <code>Hotel</code> object
	 */
	private String name;
	//@ private invariant room1 != null;
	//@ private invariant room2 != null;
	/**
	 * 2 <code>Room</code> objects
	 */
	private Room room1,room2;
	//@ private invariant password != null;
	/**
	 * variable password for <code>Password</code>
	 */
	private Password password;
		/**
		 * Creates a <code>Hotel</code> with 2 <code>Room<code> objects and a <code>Password<code>
		 * @param name is name of the object <code>Hotel</code>
		 */
	//@requires Room != null;
	//@requires Password != null;
	//@ensures getName().equals(name);
	//@ensures getPassword().testWord(Password.INITIAL);
	public Hotel (String name) {
		this.name = name;
		assert (name != null);
		password = new Password();
		assert (password != null);
		room1 = new Room(101);
		assert (room1 != null);
		room2 = new Room(102);
		assert (room2 != null);
	}
	//@ requires guest != null;
	//@ requires pass =! null;
	/**
	 * Assigns a <code>Guest</code> to a <code>Room</code> if it isn't occupied and activates <code>Safe</code> of <code>Room</code>
	 * @param pass is the input for the object <code>Password</code>
	 * @param guest is the name of the object <code>Guest</code> that wants to check in
	 * @return the <code>Room</code> object of the <code>Guest</code> that checked in or null if the <code>Guest</code> couldn't check in
	 */
	public Room checkIn (String pass, String guest) {
		assert (guest != null && pass != null);
		if (room1.getGuest() == null && password.testWord(pass)) {
			Guest guest1 = new Guest(guest);
			room1.setGuest(guest1);
			room1.getSafe().activate(pass);
			return room1;
		} if (room2.getGuest() == null && password.testWord(pass)) {
			Guest guest2 = new Guest(guest);
			room2.setGuest(guest2);
			room2.getSafe().activate(pass);
			return room2;
		} else {
			return null;
		}
	}
	//@ requires name != null;
	/**
	 * Checks out a <code>Guest</code> object for the <code>Hotel</code> object and deactivates <code>Safe</code>
	 * @param name is the name of the guest that wants to check out
	 */
	public void checkOut(String name) {
		assert (name != null);
		if (getRoom(name) == room1) {
			room1.setGuest(null);
			room1.getSafe().deactivate();
			room1.getSafe().close();
		} if (getRoom(name) == room2) {
			room2.setGuest(null);
			room2.getSafe().deactivate();
			room2.getSafe().close();
		}
	}
	//@ ensures name != null;
	/*@pure*/public String getName(){
		return name;
	}
	//@ pure
	//@ ensures \result == null || ensures \result.getGuest() == null;
	/**
	 * Checks if a there are free <code>Room</code> objects
	 * @return the <code>Room</code> if there are free rooms else null
	 */
	public Room getFreeRoom() {
		if (room1.getGuest() == null) {
			return room1;
		} if (room2.getGuest() == null) {
			return room2;
		} else {
			return null;
		}
	}
	//@ requires guest.length() >= 1;
	//@ pure
	/**
	 * Calls the <code>Room</code> object of the <code>Guest</code>
	 * @param guest is the name of the <code>Guest</code> object from which the <code>Room</code> is called
	 * @return <code>Room</code> object of the <code>Guest</code>
	 */
	public Room getRoom(String guest) {
		assert (guest.length() >= 1);
		if (room1.getGuest() != null && room1.getGuest().getName() == guest) {
			return room1;
		} if (room2.getGuest() != null && room2.getGuest().getName() == guest) {
			return room2;
		} else {
			return null;
		}
	}
	//@ pure
	/**
	 * Calls the <code>Password</code> object of the <code>Hotel</code>
	 * @return <code>Password</code> object of the <code>Hotel</code>
	 */
	//@ ensures password != null;
	public Password getPassword() {
		return password;
	}
	//@ pure
	/**
	 * Calls name of <code>Hotel</code>
	 * @return name of the <code>Hotel</code>
	 */
	//@ ensures name =! null;
	public String getHotel() {
		return name;
	}
	//@ pure
	/**
	 * Gives detailed description of <code>Room</code> objects, the name of the <code>Guest</code> and the state of the <code>Safe</code>
	 */
	public String toString() {
		assert (room1.getGuest() != null);
		assert (room2.getGuest() != null);
		return "Room "+room1.getNumber()+ ": "+ room1.getGuest().getName() + " Safe Active: " + room1.getSafe().isActive() +" Open: " + room1.getSafe().isOpen(); 
	}
}
