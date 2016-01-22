package player;

import java.util.List;
import java.util.Set;

import Qwirkle.*;

public interface Strategy {
	
	public String determineMove(Board board, Set<Tile> tile);
	

}
