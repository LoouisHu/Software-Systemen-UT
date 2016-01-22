package player;

import java.util.List;
import java.util.Set;

import Qwirkle.Board;
import Qwirkle.Move;
import Qwirkle.Tile;

public class RetardedStrategy implements Strategy {

	@Override
	public String determineMove(Board board, Set<Tile> hand) {
		// TODO Auto-generated method stub
		
		Player p = new ComputerPlayer("RS", hand);
		return null;
		
	}

}
