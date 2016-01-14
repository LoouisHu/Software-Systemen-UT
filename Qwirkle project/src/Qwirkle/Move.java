package Qwirkle;

public class Move {
	
	private Tile tile;
	private Coord coord;
	
	public Move(Tile tile, Coord coord){
		this.tile = tile;
		this.coord = coord;
	}
	
	public Tile getTile() {
		return tile;
	}
	public void setTile(Tile tile) {
		this.tile = tile;
	}
	public Coord getCoord() {
		return coord;
	}
	public void setCoord(Coord coord) {
		this.coord = coord;
	}
	
	
}
