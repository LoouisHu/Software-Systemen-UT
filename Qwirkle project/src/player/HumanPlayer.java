package player;

import java.util.List;
import java.util.ArrayList;

import controller.Client;
import model.Board;
import model.Move;
import model.Tile;
import model.Tile.Color;
import model.Tile.Shape;
import view.TUI;

public class HumanPlayer implements RealPlayer {

	private Client client;
	private String name;
	private TUI tui;
	private int score;
	private int playernumber;
	private ArrayList<Tile> hand;

	/**
	 * Bouwt een HumanPlayer met een naam en een client.
	 * @param name is de naam van de HumanPlayer.
	 * @param client is de client voor de HumanPlayer.
	 */
	public HumanPlayer(String name, Client client) {
		this.hand = new ArrayList<Tile>();
		this.score = 0;
		this.name = name;
		this.client = client;
		this.tui = client.getView();
	}
	/**
	 * Geeft een HumanPlayer een nieuwe hand met Tiles.
	 * @param newHand
	 */
	public void setHand(List<Tile> newHand) {
		hand.addAll(newHand);
	}
	/**
	 * Bepaalt zetten die een HumanPlayer op een board wil doen.
	 * @param b is een board
	 * @param hand zijn de Tiles van een HumanPlayer in zijn hand
	 * @return de zetten die een HumanPlayer wil zetten in String.
	 */
	public String determineMove(Board b, List<Tile> hand) {
		return tui.waitForMove();
	}
	/**
	 * Haalt een tile uit de hand van een HumanPlayer als hij een zet maakt.
	 * @param move is de zet die hij wil maken
	 */
	public void removeFromHandByMove(Move move) {
		Tile removedTile = null;
		for (Tile t: hand) {
			if (t.getColor() == move.getTile().getColor() &&
					t.getShape() == move.getTile().getShape()) {
				removedTile = t;
			}
		}
		hand.remove(removedTile);
	}
	/**
	 * Haalt tiles uit de hand van een HumanPlayer als hij ruilt.
	 * @param moves
	 */
	public void removeFromHandBySwap(List<Move> moves) {
		for (Move m: moves) {
			Color c = m.getTile().getColor();
			Shape s = m.getTile().getShape();
			for (int i = 0; i < hand.size(); i++) {
				if (hand.get(i).getColor() == c && hand.get(i).getShape() == s) {
					hand.remove(i);
				}
			}
		}
	}
	
	/* @pure */public String getName() {
		return name;
	}

	/* @pure */public int getScore() {
		return score;
	}

	/* @pure */public ArrayList<Tile> getHand() {
		return hand;
	}


	/* @pure */public Client getClient() {
		return client;
	}

	/* @pure */public int getNumber() {
		return playernumber;
	}

	@Override
	public void updateScore(int score) {
		this.score += score;
	}

	@Override
	public void setNumber(int playerno) {
		playernumber = playerno;
	}
}
