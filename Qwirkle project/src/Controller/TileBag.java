package Controller;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import Qwirkle.Tile;
import Qwirkle.Tile.Color;
import Qwirkle.Tile.Shape;
//TODO gebruiken voor de server;
public class TileBag {
	
	// Aantal stenen
	public static final int SIZE = 108;
			
	//Aantal stenen in hand
	public static final int SIZE_HAND = 6;
	
	//Tiles dat in de bag zitten
	private ArrayList<Tile> tiles;
	
	//Creates a bag with 108 tiles in it :)
	public TileBag() {
		this.tiles = new ArrayList<>(SIZE);
		
		for (Tile.Color c : Tile.Color.values()){
			for( Tile.Shape s : Tile.Shape.values()){
				this.tiles.add(new Tile(c, s));
			}
		}
	}
	
	// Draw the first tile from the bag and delete it
	public Tile drawTile(){
		return this.tiles.remove(0);
	}
	
	//Draw first round 6 tiles;
	public Set<Tile> drawSix(){
		Set<Tile> hand = new HashSet<>();
		for (int i = 0; i < SIZE_HAND; i++){
			hand.add(this.drawTile());
		}
		return hand;
	}
	
	//shuffles the tiles
	public void shuffle(){
		Collections.shuffle(this.tiles);
	}
	
	//return amount of tiles
	public int remainingTiles(){
		return this.tiles.size();
	}
	

}
