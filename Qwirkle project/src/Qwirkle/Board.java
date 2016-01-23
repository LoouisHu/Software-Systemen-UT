package Qwirkle;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import Qwirkle.Tile.Color;
import Qwirkle.Tile.Shape;

public class Board {

	public static Tile[][] boardSpaces;
	public static final int DIM = 183;
	public static final int powerMoveLength = 6;

	//@public invariant boardSpaces.length == DIM;
	
	//
	public Board() {
		boardSpaces = new Tile[DIM][DIM];
	}

	public boolean validMove(/*@ non_null */Move move) {
		return validMove(move, new ArrayList<Move>());
	}

	/*
	 * @ 
	 */
	public boolean validMove(/*@ non_null */Move theMove,/*@ non_null */ List<Move> movesMade) {
		boolean firstMove = (boardSpaces[91][91] == null);
		boolean answer = true;
		boolean oldY = true;
		boolean oldX = true;
		if (!firstMove) {
			for (Move m : movesMade) {
				if (m.getCoord().getX() != theMove.getCoord().getX()) {
					oldX = false;
				}
				if (m.getCoord().getY() == theMove.getCoord().getY()) {
					oldY = false;
				}
			}
			if (!oldX && !oldY) {
				answer = false;
			}

			if (boardSpaces[theMove.getCoord().getX()][theMove.getCoord().getY()] != null) {
				answer = false;
			}
			int adjecends = 0;
			for (int i = 0; i < 4; i++) {
				Coord c = theMove.getCoord().getAdjacentCoords()[i];
				if (boardSpaces[c.getX()][c.getY()] != null) {
					adjecends++;
				}
			}
			if (adjecends == 0) {
				answer = false;
			}
			if (!(inLineV(theMove) && inLineH(theMove))) {
				answer = false;
			}
		} else if (theMove.getCoord().getX() != 91 || theMove.getCoord().getY() != 91) {
			answer = false;
		}

		return answer;
	}
/*
 * @ requires
 * check of de eerste naast m klopt met de regels, maar de volgende daar naast niet
 */
	
	
	public boolean inLineV(/*@ non_null */Move m) {
		Coord c = m.getCoord();
		Tile t = m.getTile();
		ArrayList<Tile> tiles = new ArrayList<Tile>();
		int x = c.getX();
		int y = c.getY();

		for (int i = 1; i < powerMoveLength; i++) {
			Tile tit = boardSpaces[x][y + i];
			if (tit == null) {
				break;
			}
			tiles.add(tit);
		}
		for (int i = 1; i < powerMoveLength; i++) {
			Tile tit = boardSpaces[x][y - i];
			if (tit == null) {
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
		if (answer) {
			for (Tile tt : tiles) {
				if (tt.getShape() == t.getShape() && !shapeRelation) {
					answer = false;
					break;
				} else if (tt.getColor() == t.getColor() && !colorRelation) {
					answer = false;
					break;
				}
			}
		}
		return answer;
	}

	public boolean inLineH(/*@ non_null */Move m) {
		Coord c = m.getCoord();
		Tile t = m.getTile();
		ArrayList<Tile> tiles = new ArrayList<Tile>();
		int x = c.getX();
		int y = c.getY();

		for (int i = 1; i < powerMoveLength; i++) {
			Tile tit = boardSpaces[x + i][y];
			if (tit == null) {
				break;
			}
			tiles.add(tit);
		}
		for (int i = 1; i < powerMoveLength; i++) {
			Tile tit = boardSpaces[x - i][y];
			if (tit == null) {
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
		if (answer) {
			for (Tile tt : tiles) {
				if (tt.getShape() == t.getShape() && !shapeRelation) {
					answer = false;
					break;
				} else if (tt.getColor() == t.getColor() && !colorRelation) {
					answer = false;
					break;
				}
			}
		}
		return answer;
	}

	public void boardAddMove(/*@ non_null */Move move) {
		boardSpaces[move.getCoord().getX()][move.getCoord().getY()] = move.getTile();
	}

	public void boardRemove(/*@ non_null */Coord coord) {
		boardSpaces[coord.getX()][coord.getY()] = null;
	}

	public Set<Move> getUsedSpaces() {
		Set<Move> result = new HashSet<Move>();
		for (int i = 0; i < DIM; i++) {
			for (int j = 0; j < DIM; j++) {
				if (boardSpaces[i][j] != null) {
					result.add(new Move(boardSpaces[i][j], new Coord(i, j)));
				}
			}
		}
		return result;
	}

	public boolean gameOver() {
		boolean answer = false;
		return answer;
	}

	public boolean hasWinner() {
		boolean answer = false;
		return answer;
	}

	public void Start() {

	}

	public String toString() {
		String result = "";
		String line = "";
		for(int i = 0; i < DIM*2; i++) {
			line += "-";
		}
		result += line;
		for(int y = 0; y < DIM; y++) {
			result += "|";
			for(int x = 0; x < DIM; x++) {
				Tile t = boardSpaces[x][y];
				if(t != null) {
					result += t.getShape().c + "|";
					System.out.println(t.getShape().c);
				} else {
					result += " |";
				}
			}
			result += "\n" + line + "\n";
		}
		return result;
	}
	
	public static void main(String args[]) {
		Board b = new Board();
		b.boardAddMove(new Move(new Tile(Color.BLUE, Shape.STAR), new Coord(0,0)));
		System.out.println(b.toString());
	}
}