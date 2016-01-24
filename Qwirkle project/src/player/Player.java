package player;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import Controller.Game;
import Qwirkle.Board;
import Qwirkle.Coord;
import Qwirkle.Move;
import Qwirkle.Tile;

public abstract class Player {
	
 // -- Instance variables -----------------------------------------

	 private String name;
	 
	 private List<Tile> hand;
	 
	 private Board deepCopy;
	 
	 private Board board;
	 
	 private Game game;
	 
	 private List<Move> currentMoves;

	 
	 //-----Constructor------
	 
	 public Player(String name, List<Tile> hand, Board board, Game game){
		 this.name = name;
		 this.hand = hand;
		 this.board = board;
		 this.game = game;
		 currentMoves = new ArrayList<Move>();
	 }
	 //------Queries-------
	 public String getName(){
		 return this.name;
	 }
	
	 public List<Tile> getHand(){
		 return this.hand;
	 }
	 
	 //----Setters-----
	 
	 public void setHand(List<Tile> newHand){
		 hand.addAll(newHand);
	 }
	
	 //----Methods-----
	 
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
	
	public Board getBoard(){
		return board;
	}
	
}

