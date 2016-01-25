package player;

import java.util.List;

import controller.Game;
import model.*;

public interface Strategy {
	
	public Move determineMove(Board board, List<Tile> hand);

}
