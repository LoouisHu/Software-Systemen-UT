package player;

import java.util.List;

import Controller.Game;
import Qwirkle.*;

public interface Strategy {
	
	public Move determineMove(Board board, List<Tile> hand, Game game);

}
