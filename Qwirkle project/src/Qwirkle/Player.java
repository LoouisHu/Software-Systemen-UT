package Qwirkle;

import java.util.List;
import java.util.Set;

public abstract class Player {
	
 // -- Instance variables -----------------------------------------

	 private String name;
	 private Set<Tile> hand;
	 private Board deepCopy;
	 private Board board;
	 private List<Move> currentMoves;
	 
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
	    
	 
	public void MakeMove(Tile tile, Coord coord){
		Move movie = new Move(tile, coord);
		if(currentMoves.size() == 0){
			deepCopy = board;
		}
		if(this.getHand().contains(tile) && deepCopy.validMove(movie, currentMoves)){
			deepCopy.boardAddMove(movie);
		}
	}
	
	public void confirmTurn(){
		
	}
	
	public void TradeTiles(){
		
	}
}

