package player;

import java.util.List;

import controller.Game;
import model.Board;
import model.Coord;
import model.Move;
import model.Tile;

public class ComputerPlayer extends Player {
	
	private Strategy strat;
	
	public ComputerPlayer(String name, Board board){
		super(name, board);
		this.strat = new RetardedStrategy();
	}
	
	public Move makeMove(Tile tile, Coord coord){
		return strat.determineMove(super.getBoard(), super.getHand());
	}
}