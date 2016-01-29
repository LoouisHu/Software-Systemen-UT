package controller;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import model.Board;
import model.Tile;
import model.TileBag;
import player.Player;
import player.PlayerScore;

public class Game {

	private List<Tile> tiles;

	private List<PlayerScore> playerScores;

	private int turn;

	private TileBag tilebag;

	private Board board;
	
	private int amountOfPlayers;

	public Game(int aantalSpelers) {
		this.amountOfPlayers = aantalSpelers;
		tilebag = new TileBag();
		board = new Board();
		turn = 0;
		playerScores = new ArrayList<PlayerScore>(aantalSpelers);
	}

	public void nextTurn() {
		turn++;
	}

	/* @ pure */
	public int getTurn() {
		return turn;
	}

	public List<PlayerScore> getPlayerScores() {
		return playerScores;
	}

	public boolean gameOver() {
		return false;
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
	
	public int remainingTiles() {
		return getTileBag().getTileBagSize();
	}
	
	public void addPlayers(){
		for (PlayerScore p: playerScores) {
			Player p2 = new HumanPlayer();
			p = new PlayerScore();
		}
	}
}