package model;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

//TODO gebruiken voor de server;
public class TileBag {

	// @ private invariant tiles != null;

	// Aantal stenen
	public static final int SIZE = 108;

	// Aantal stenen in hand
	public static final int SIZE_HAND = 6;

	// Tiles dat in de bag zitten
	private ArrayList<Tile> tiles;

	/**
	 * Maakt een nieuwe bag en vult het met de 108 tiles.
	 */

	public TileBag() {
		this.tiles = new ArrayList<Tile>();
		for (Tile.Color c : Tile.Color.values()) {
			for (Tile.Shape s : Tile.Shape.values()) {
				for (int i = 0; i < 3; i++) {
					this.tiles.add(new Tile(c, s));
				}
			}
		}
	}

	/**
	 * Retourneert een lijst met willekeurige tiles.
	 * 
	 * @param amount
	 */
	// @ requires amount > 0 && amount <= Player.SIZE_HAND;
	// @ ensures \result != null;
	// @ ensures \result.size() == amount;
	// @ ensures getSize() == (amount >= getSize() ? \old(getSize()) - amount :
	// 0);
	public List<Tile> getTiles(int amount) {
		List<Tile> hand = new ArrayList<Tile>();
		for (int i = 0; i < amount && getTileBagSize() > 0; i++) {
			hand.add(tiles.get(0));
			tiles.remove(0);
		}
		return hand;
	}

	/**
	 * De TileBag wordt geschud.
	 */
	public void shuffle() {
		Collections.shuffle(this.tiles);
	}
	/*pure*/
	public int getTileBagSize() {
		return this.tiles.size();
	}

	/**
	 * Kijkt of de bag leeg is.
	 * 
	 * @return
	 */
	public boolean isEmpty() {
		return this.tiles.isEmpty();
	}

	/**
	 * Keert de tiles weer terug in de stapel en schudt ze.
	 * 
	 * @param tiles
	 *            de tiles die je in je hand had oid.
	 */
	// @ requires tiles != null;
	// @ ensures getSize() == \old(getSize()) + tiles.size();
	public void returnTiles(List<Tile> t) {
		tiles.addAll(t);
		shuffle();
	}
}
