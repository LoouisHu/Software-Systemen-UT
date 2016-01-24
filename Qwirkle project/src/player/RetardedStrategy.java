package player;

import java.util.List;

import Controller.Game;
import Qwirkle.Board;
import Qwirkle.Coord;
import Qwirkle.Move;
import Qwirkle.Tile;

public class RetardedStrategy implements Strategy {

	@Override
	public Move determineMove(Board board, List<Tile> hand, Game game) {
		// TODO Auto-generated method stub
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
		if (result == null){
			for (int l = 0; l < hand.size(); l++){
				game.swap(hand);
			}
		}
		return result;
	}

}
