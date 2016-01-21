package player;

import java.util.List;
import java.util.Set;

import Qwirkle.Board;
import Qwirkle.Move;
import Qwirkle.Tile;

public class RetardedStrategy implements Strategy {
	
	private Player player;

	public RetardedStrategy(Player player) {
		this.player = player;
	}

	@Override
	public String determineMove(Board board, Set<Tile> hand) {
		// TODO Auto-generated method stub
		
		Player p = new ComputerPlayer("RS", hand);
		return null;
	}

	@Override
	public List<Move> strategyPlay(Board board) {
		// TODO Auto-generated method stub
		return null;
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
