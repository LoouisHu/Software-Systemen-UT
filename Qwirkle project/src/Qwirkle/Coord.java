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
}
