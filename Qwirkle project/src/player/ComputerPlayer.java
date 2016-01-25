package player;

import java.util.List;

import controller.Game;
import model.Board;
import model.Tile;

public class ComputerPlayer extends Player {
	
	private Strategy strat;
	
	public ComputerPlayer(String name, List<Tile> hand, Board board, Game game){
		super(name, hand, board, game);
		this.strat = new RetardedStrategy();
	}
	
	
}
