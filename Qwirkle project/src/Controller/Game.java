package Controller;

import java.util.Map;
import java.util.Set;

import Qwirkle.Tile;
import player.Player;

public class Game {

	private Set<Tile> tiles;
	
	private Map<Player, Integer> scores;
	
	private int turn;
	
	private TileBag tilebag;
	
	public Game(int aantalspelers) {
		tilebag = new TileBag();
	}
	
	public void nextTurn(){
		turn++;
	}
	
	public int getTurn(){
		return turn;
	}
	
	public Map<Player, Integer> getScores(){
		return scores;
	}
	
	public 
	
	public boolean gameOver() {
		boolean answer = false;
		return answer;
	}

	public boolean hasWinner() {
		boolean answer = false;
		return answer;
	}
}
