package player;

import java.util.List;
import java.util.Set;

import Qwirkle.Board;
import Qwirkle.Move;
import Qwirkle.Tile;

public class ComputerPlayer extends Player implements Strategy{
	
	private Strategy strat;

	public ComputerPlayer(String name, Set<Tile> hand) {
		super(name, hand);
		// TODO Auto-generated constructor stub
	}
	
	public ComputerPlayer(String name, Set<Tile> hand, Strategy strat){
		super(name, hand);
		this.strat = strat;
	}


	@Override
	public String determineMove(Board board, Set<Tile> tile) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<Move> strategyPlay(Board board, List<Tile> hand, Player player, int tileSize) {
		// TODO Auto-generated method stub
		return null;
	}

}
