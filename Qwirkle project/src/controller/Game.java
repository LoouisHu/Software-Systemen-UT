package controller;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import model.Board;
import model.Tile;
import player.Player;

public class Game {

	private List<Tile> tiles;

	private Map<Player, Integer> scores;

	private int turn;

	private TileBag tilebag;

	private Player player;

	private Board board;
	
	private int aantalspelers;

	public Game(int aantalspelers) {
		tilebag = new TileBag();
		this.aantalspelers = aantalspelers;
	}

	public void nextTurn() {
		turn = turn%aantalspelers;
	}

	/* @ pure */
	public int getTurn() {
		return turn;
	}

	public Map<Player, Integer> getScores() {
		return scores;
	}

	public boolean gameOver() {
		for
		return tilebag.isEmpty()&& 1 vd handen is leeg;
	}

	public boolean hasWinner() {
		boolean answer = false;
		return answer;
	}

	/* @ pure */
	public Board getBoard() {
		return board;
	}

	/* @ pure */
	public TileBag getTileBag() {
		return tilebag;
	}

	public List<Tile> swap(List<Tile> tilesSwap) {
		List<Tile> result = new ArrayList<Tile>();
		for (int i = 0; i < tiles.size(); i++) {
			 //result.(tilebag.returnTiles(tilesSwap)));
			return result;
		}
		for (Tile t : tilesSwap) {
			// tilebag.returnTile(t);
		}
		tilebag.shuffle();
		return result;
	}
}
