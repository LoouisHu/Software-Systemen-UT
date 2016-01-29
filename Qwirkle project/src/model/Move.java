package model;

public class Move {

	private Tile tile;
	private Coord coord;

	public Move(Tile tile, Coord coord) {
		this.tile = tile;
		this.coord = coord;
	}
	
	public Move(Tile t) {
		this.tile = t;
	}
	
	/*@pure*/
	public Tile getTile() {
		return tile;
	}
	/*@pure*/
	public void setTile(Tile tile) {
		this.tile = tile;
	}
	/*@pure*/
	public Coord getCoord() {
		return coord;
	}
	/* 
	 * @requires coord != null;	
	 * @ensures getCoord() == coord;
	 */
	public void setCoord(Coord coord) {
		this.coord = coord;
	}

}
