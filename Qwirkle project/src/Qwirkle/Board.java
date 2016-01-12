package Qwirkle;

import java.util.ArrayList;
import java.util.List;

public class Board {
	
	public static String[][] boardSpaces;
	public static List usedSpaces;
	private int x;
	private int y;
	public static final int DIM = 183;
	
	public Board(){
		usedSpaces = new ArrayList<coord>();
		boardSpaces = new String[DIM][DIM];
	}
	
	public boolean validMove(){
		boolean answer = true;
		if (usedSpaces.contains(coord(x,y))){
			answer = false;
		}
		return answer;
	}
	
	public boolean validXMove(){
		boolean answer = true;
		move (Tile, x, y);
		if(!usedSpaces.contains(coord(x,y))){
			
		}
		return answer;
	}
	
	public boolean validYMove(){
		boolean answer = true;
		if(){
			
		}
		return answer;
	}
	
	public boolean gameOver(){
		boolean answer = false;
		return answer;
	}
	
	public boolean hasWinner(){
		boolean answer = false;
		return answer;
	}
	
	public void Start(){
		
	}
	

}
