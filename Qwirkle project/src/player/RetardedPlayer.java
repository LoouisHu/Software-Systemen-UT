package player;

import java.util.List;

import controller.Client;
import model.Board;
import model.Coord;
import model.Move;
import model.Tile;
import view.TUI;

public class RetardedPlayer extends HumanPlayer {

	private int playernumber;
	private int score;
	private TUI view;

	public RetardedPlayer(String name, Client client) {
		super(name, client);
	}

	@Override
	public String determineMove(Board board, List<Tile> hand) {
		String result = null;
		boolean isFound = false;
		for (int i = 0; i < board.getUsedSpaces().size() && !isFound; i++) {
			Move m = board.getUsedSpaces().get(i);
			for (int j = 0; j < 4 && !isFound; j++) {
				int x = m.getCoord().getAdjacentCoords()[j].getX();
				int y = m.getCoord().getAdjacentCoords()[j].getY();
				for (int k = 0; k < hand.size() && !isFound; k++) {
					Move tempmove = new Move(hand.get(k), new Coord(x, y));
					if (board.validMove(tempmove)) {
						isFound = true;
						result = tempmove.getTile().toString() + " " +
						tempmove.getCoord().getX() + " " + tempmove.getCoord().getY();
					}
				}
			}
		}
		return result;
	}
}
