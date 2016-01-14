package Qwirkle;

import java.util.Set;

public abstract class Player {
	
 // -- Instance variables -----------------------------------------

	 private String name;
	 private Set<Tile> hand;
	 private Board deepcopy;
	 private Board board;
	 
	 public Player(String name, Set<Tile> hand){
		 this.name = name;
		 this.hand = hand;
	 }
	 
	 public String getName(){
		 return name;
	 }
	
	 public Set<Tile> getHand(){
		 return hand;
	 }
	    
	 
	public void MakeMove(){
		
	}
	
	public void TradeTiles(){
		
	}
}

