package player;

import java.util.List;

import Qwirkle.Board;
import Qwirkle.Move;

public interface Strategy {
	
	public String determineMove(Board board);
	
	public List<Move> strategyPlay(Board board);

}
