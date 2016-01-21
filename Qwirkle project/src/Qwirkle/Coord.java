package Qwirkle;

public class Coord {

	private int horizontal;
	private int vertical;
	private static final int DIM = 183;
	
	public Coord(int x, int y){
		horizontal = x;
		vertical = y;
}
	public int getX(){
		return horizontal;
	}
	public int getY(){
		return vertical;
	}
	public Coord[] getAdjacentCoords(){
		Coord[] coords = new Coord[4];
		if(horizontal != DIM){
		coords[0] = new Coord(horizontal+1,vertical);
		}
		if(horizontal != 0){
			coords[1] = new Coord(horizontal-1,vertical);			
		}
		if(vertical != DIM){
			coords[2] = new Coord(horizontal,vertical+1);
		}
		if(vertical != 0){
			coords[3] = new Coord(horizontal,vertical-1);
		}
		return coords;

	}
}
