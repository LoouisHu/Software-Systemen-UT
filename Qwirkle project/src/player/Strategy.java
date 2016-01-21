package player;

import java.util.List;
import java.util.Set;

import Qwirkle.*;

public interface Strategy {
	
	public String determineMove(Board board, Set<Tile> tile);
	
	public List<Move> strategyPlay(Board board, List<Tile> hand, Player player, int tileSize);

}
