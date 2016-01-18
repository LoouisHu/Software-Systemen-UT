package Qwirkle;

import java.util.Map;
import java.util.Set;

public class Game {

	private Set<Tile> tiles;
	
	private Map<Player, Integer> scores;
	
	private int turn;
	
	
	public void nextTurn(){
		turn++;
	}
	
	public int getTurn(){
		return turn;
	}
	
	public Map<Player, Integer> getScores(){
		return scores;
	}
	
}
