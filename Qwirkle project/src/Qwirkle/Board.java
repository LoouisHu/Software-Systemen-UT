package Qwirkle;

import java.util.ArrayList;
import java.util.List;
public class Board {
	
	public static Tile[][] boardSpaces;
	public static final int DIM = 183;
	public static final int powerMoveLength = 6;	
	public Board(){
		boardSpaces = new Tile[DIM][DIM];
	}
	

	public boolean validMove(Move move) {
		return validMove(move, new ArrayList<Move>());
	}
	

	public boolean validMove(Move theMove, List<Move> movesMade){
		boolean answer = true;
		boolean oldY = true;
		boolean oldX = true;
		for (Move m : movesMade) {
			if(m.getCoord().getX() != theMove.getCoord().getX()) {
				oldX = false;
			}
			if(m.getCoord().getY() == theMove.getCoord().getY()) {
				oldY = false;
			}
		}
		if (!oldX && !oldY) {
			answer = false;
		}
		if (boardSpaces[theMove.getCoord().getX()][theMove.getCoord().getY()] != null){
			answer = false;
		}
		int adjecends =0;
		for(int i=0; i<4; i++){
			Coord c = theMove.getCoord().getAdjecendCoords()[i];
		    if(boardSpaces[c.getX()][c.getY()] != null){
		    	adjecends++;
		    }
		}
		if(adjecends == 0){
			answer = false;
		}
		if(!(inLineV(theMove) && inLineH(theMove))){
			answer = false;
		}
		
		return answer;
	}
	
	
	public boolean inLineV(Move m){
	Coord c = m.getCoord();
	Tile t = m.getTile();
	ArrayList<Tile> tiles = new ArrayList<Tile>();
	int x = c.getX();
	int y = c.getY();
	
	for(int i=1; i<powerMoveLength; i++){
		Tile tit = boardSpaces[x][y+i];
		if(tit == null){
			break;
		}
		tiles.add(tit);
	}
	for(int i=1; i<powerMoveLength; i++){
		Tile tit = boardSpaces[x][y-i];
		if(tit == null){
			break;
		}
		tiles.add(tit);
	}
	boolean shapeRelation = (t.getShape() == tiles.get(0).getShape());
	boolean colorRelation = (t.getColor() == tiles.get(0).getColor());
	boolean answer = true;
	if (!(shapeRelation ^ colorRelation)) {
		answer = false;
	}
	if(answer){
	for(Tile tt : tiles){
		if(tt.getShape() == t.getShape() && !shapeRelation){
			answer = false;
			break;
		}else if(tt.getColor() == t.getColor() && !colorRelation){
			answer = false;
			break;
		}
	}
	}
	return answer;
	}
	
	public boolean inLineH(Move m){
		Coord c = m.getCoord();
		Tile t = m.getTile();
		ArrayList<Tile> tiles = new ArrayList<Tile>();
		int x = c.getX();
		int y = c.getY();
		
		for(int i=1; i<powerMoveLength; i++){
			Tile tit = boardSpaces[x+i][y];
			if(tit == null){
				break;
			}
			tiles.add(tit);
		}
		for(int i=1; i<powerMoveLength; i++){
			Tile tit = boardSpaces[x-i][y];
			if(tit == null){
				break;
			}
			tiles.add(tit);
		}
		boolean shapeRelation = (t.getShape() == tiles.get(0).getShape());
		boolean colorRelation = (t.getColor() == tiles.get(0).getColor());
		boolean answer = true;
		if (!(shapeRelation ^ colorRelation)) {
			answer = false;
		}
		if(answer){
		for(Tile tt : tiles){
			if(tt.getShape() == t.getShape() && !shapeRelation){
				answer = false;
				break;
			}else if(tt.getColor() == t.getColor() && !colorRelation){
				answer = false;
				break;
			}
		}
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
