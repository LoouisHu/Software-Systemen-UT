package player;

import java.util.ArrayList;
import java.util.List;

import model.Move;
import model.Tile;

public class SocketPlayer implements RealPlayer {

	private String name;
	private int playernumber;
	private int score;
	private List<Tile> hand;
	

	public SocketPlayer(String name, int playernumber) {
		this.name = name;
		this.playernumber = playernumber;
		this.score = 0;
		this.hand = new ArrayList<Tile>();
	}
	
	public SocketPlayer() {
		this.score = 0;
	}

	/**
	 * Geeft een SocketPlayer een nieuwe hand van tiles.
	 * @param newhand is een lijst van tiles
	 */
	public void setHand(List<Tile> newhand) {
		hand = newhand;
	}
	/**
	 * Ruilt tiles uit een SocketPlayer's hand met stenen uit de tilebag.
	 * @param newtiles
	 * @param swaps
	 */
	public void swapHand(List<Tile> newtiles, List<Move> swaps) {
		removeFromHandMoves(swaps);
		hand.addAll(newtiles);
	}
	/**
	 * Haalt tiles uit de hand van een SocketPlayer's hand.
	 * @param moves
	 */
	public void removeFromHandMoves(List<Move> moves) {
		for (Move m : moves) {
			for (int i = 0; i < hand.size(); i++) {
				if (hand.get(i).getColor() == m.getTile().getColor()
						&& hand.get(i).getShape() == m.getTile().getShape()) {
					hand.remove(i);
				}
			}
		}
	}
	/**
	 * Plaatst een SocketPlayer's tiles op de board.
	 * @param moves
	 * @param newcards
	 */
	public void placeTiles(List<Move> moves, List<Tile> newcards) {
		outer : for (Move m: moves) {
			for (int i = 0; i < hand.size(); i++) {
				if (m.getTile().getColor().equals(hand.get(i).getColor()) 
						  && m.getTile().getShape().equals(hand.get(i).getShape())) {
					hand.remove(i);
					continue outer;
				}
			}
		}
		hand.addAll(newcards);
	}
	
	@Override
	public int getScore() {
		return score;
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public int getNumber() {
		return playernumber;
	}

	@Override
	public void updateScore(int score) {
		this.score = score;
	}

	@Override
	public void setNumber(int playerno) {
		this.playernumber = playerno;
	}
	
	public void setName(String name) {
		this.name = name;
	}
	
	public List<Tile> getHand() {
		return hand;
	}

}
