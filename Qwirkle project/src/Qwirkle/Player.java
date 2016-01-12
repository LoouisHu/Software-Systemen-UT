package Qwirkle;

public abstract class Player {
	
 // -- Instance variables -----------------------------------------

	 private String name;
	 private Tile[] hand;
	 
	 public Player(String name, Tile[] hand){
		 this.name = name;
		 this.hand = hand;
	 }
	 
	 public String getName(){
		 return name;
	 }
	
	 public Tile[] getHand(){
		 return hand;
	 }
	    
}

