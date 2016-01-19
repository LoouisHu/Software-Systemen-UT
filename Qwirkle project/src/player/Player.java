package player;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import Qwirkle.Board;
import Qwirkle.Coord;
import Qwirkle.Move;
import Qwirkle.Tile;

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
		 currentMoves = new ArrayList<Move>();
		 board = new Board();
	 }
	 
	 public String getName(){
		 return name;
	 }
	
	 public Set<Tile> getHand(){
		 return hand;
	 }
	 
	 public void setHand(Set<Tile> newHand){
		 hand.addAll(newHand);
	 }
	    
	 
	public void makeMove(Tile tile, Coord coord){
		Move movie = new Move(tile, coord);
		if(currentMoves.size() == 0){
			deepCopy = board;
		}
		if(hand.contains(tile) && board.validMove(movie, currentMoves)){
			board.boardAddMove(movie);
			currentMoves.add(movie);
			hand.remove(movie.getTile());
		}
	}
	
	public void makeMove(Move move){
		makeMove(move.getTile(), move.getCoord());
	}
	
	public void undoMove(){
		Move lastMove = currentMoves.get(currentMoves.size()-1);
		board.boardRemove(lastMove.getCoord());
		hand.add(lastMove.getTile());
	    currentMoves.remove(lastMove);
	}
	
	public void confirmTurn(){
//      send board to server
		currentMoves.removeAll(currentMoves);
	}
	
}

