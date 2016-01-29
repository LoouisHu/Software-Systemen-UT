package player;

import java.util.List;

import controller.Game;
import model.Board;
import model.Coord;
import model.Move;
import model.Tile;

public class RetardedStrategy implements Strategy {

	@Override
	public Move determineMove(Board board, List<Tile> hand) {
		Move result = null;
		boolean isFound = false;
		for (int i = 0; i < board.getUsedSpaces().size() && !isFound; i++) {
			Move m = board.getUsedSpaces().get(i);
			for (int j = 0; j < 4 && !isFound; i++) {
				int x = m.getCoord().getAdjacentCoords()[j].getX();
				int y = m.getCoord().getAdjacentCoords()[j].getY();
				for (int k = 0; k < hand.size() && !isFound; k++) {
					Move tempmove = new Move(hand.get(k), new Coord(x, y));
					if (board.validMove(tempmove)) {
						isFound = true;
						result = tempmove;
					}

				}
			}
		}
		if (result == null) {
			
		}
		return result;
	}

}
