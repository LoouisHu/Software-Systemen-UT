package player;

import java.util.List;
import java.util.Set;

import Qwirkle.*;

public interface Strategy {
	
	public Move determineMove(Board board, List<Tile> hand);

}
