package Controller;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import Qwirkle.Board;
import Qwirkle.Tile;
import player.Player;

public class Game {

	private Set<Tile> tiles;
	
	private Map<Player, Integer> scores;
	
	private int turn;
	
	private TileBag tilebag;
	
	private Player player;
	
	private Board board;
	
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
	
	public boolean gameOver() {
		return false;
	}

	public boolean hasWinner() {
		boolean answer = false;
		return answer;
	}
	
	public Board getBoard() {
		return board;
	}
	
	public List<Tile> swap(List<Tile> tiles) {
		List<Tile> result = new ArrayList<Tile>();
		for(int i = 0; i < tiles.size(); i++) {
			result.add(tilebag.drawTile());
		}
		for(Tile t: tiles) {
			tilebag.returnTile(t);
		}
		tilebag.shuffle();
		return result;
	}
}
