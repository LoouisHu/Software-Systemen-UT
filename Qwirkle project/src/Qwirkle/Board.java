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

	// @public invariant boardSpaces.length == DIM;

	//
	public Board() {
		boardSpaces = new Tile[DIM][DIM];
	}	

	/*@pure*/public boolean validMove(Move move) {
		return validMove(move, new ArrayList<Move>());
	}

	/*
	 * @
	 */
	/*@pure*/public boolean validMove(Move theMove, List<Move> movesMade) {
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
			int adjacent = 0;
			for (int i = 0; i < 4; i++) {
				Coord c = theMove.getCoord().getAdjacentCoords()[i];
				if (boardSpaces[c.getX()][c.getY()] != null) {
					adjacent++;
				}
			}
			if (adjacent == 0) {
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
	 * @ requires check of de eerste naast m klopt met de regels, maar de
	 * volgende daar naast niet
	 */

	/*@pure*/public boolean inLineV(Move m) {
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

	/*@pure*/public boolean inLineH(Move m) {
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

	/**
	 * laat zien of een veld leeg is.
	 * 
	 * @param x
	 *            de x-coördinaat
	 * @param y
	 *            de y-coördinaat
	 * @return true als het veld leeg is
	 */
	/*
	 * @ requires isField(x, y);
	 * 
	 * @ ensures \result == (getField(x, y) == null);
	 */
	/* @pure */
	public Boolean isEmptyField(int x, int y) {
		return getField(x, y) == null;
	}

	/**
	 * geeft true als een rij helemaal leeg is.
	 * 
	 * @param x
	 *            geeft aan welke rij je bekijkt.
	 * @return true als een rij helemaal leeg is.
	 */
	/*
	 * @ requires 0 <= x & x <= DIM;
	 * 
	 * @ ensures (\forall int y; 0 <= y & y < DIM; this.getBlock()[x][y] == null
	 * ==> \result == true);
	 */
	/* @pure */
	public boolean emptyXRow(int x) {
		boolean empty = true;
		for (int i = 0; i < DIM; i++) {
			if (!isEmptyField(x, i)) {
				empty = false;
				break;
			}
		}
		return empty;
	}

	/**
	 * geeft true als een kolom helemaal leeg is.
	 * 
	 * @param y
	 *            geeft aan welke rij je bekijkt.
	 * @return true als een rij helemaal leeg is.
	 */
	/*
	 * @ requires 0 <= y & y <= DIM;
	 * 
	 * @ ensures (\forall int x; 0 <= x & x < DIM; this.getTile()[x][y] == null
	 * ==> \result == true);
	 */
	/* @pure */
	public boolean emptyYRow(int y) {
		boolean empty = true;
		for (int i = 0; i < DIM; i++) {
			if (!isEmptyField(i, y)) {
				empty = false;
				break;
			}
		}
		return empty;
	}

	/*@pure*/public Tile getField(int x, int y) {
		return boardSpaces[x][y];
	}

	public void boardAddMove(Move move) {
		boardSpaces[move.getCoord().getX()][move.getCoord().getY()] = move.getTile();
	}

	public void boardRemove(Coord coord) {
		boardSpaces[coord.getX()][coord.getY()] = null;
	}

	/*@pure*/public List<Move> getUsedSpaces() {
		List<Move> result = new ArrayList<Move>();
		for (int i = 0; i < DIM; i++) {
			for (int j = 0; j < DIM; j++) {
				if (boardSpaces[i][j] != null) {
					result.add(new Move(boardSpaces[i][j], new Coord(i, j)));
				}
			}
		}
		return result;
	}

	/* @ ensures \result < DIM; */
	/* @pure */public int lowestX() {
		int x = 92;
		while (!this.emptyXRow(x)) {
			x--;
		}
		return x;
	}

	/* @ ensures \result < DIM; */
	/* @pure */public int highestX() {
		int x = 92;
		while (!this.emptyXRow(x)) {
			x++;
		}
		return x;
	}

	/* @ ensures \result < DIM; */
	/* @pure */public int lowestY() {
		int y = 92;
		while (!this.emptyYRow(y)) {
			y--;
		}
		return y;
	}

	/* @ ensures \result < DIM; */
	/* @pure */public int highestY() {
		int y = 92;
		while (!this.emptyYRow(y)) {
			y++;
		}
		return y;
	}

	/*@pure*/public String toString() {
		String result = "y\\x";
		for (int y = lowestY(); y <= highestY(); y++) {
			result = result.concat(String.format("|%03d", y));
		}
		result = result.concat("|\n---");

		for (int y = lowestY(); y <= highestY(); y++) {
			result = result.concat("+---");
		}
		result = result.concat("+\n");

		for (int x = lowestX(); x <= highestX(); x++) {
			result = result.concat(String.format("%03d", x));
			for (int y = lowestY(); y <= highestY(); y++) {
				Tile t = boardSpaces[x][y];
				if (t != null) {
					result = result.concat("| " + t.toString());
				} else {
					result = result.concat("|   ");
				}
			}
			result = result.concat("|\n---");
			for (int y = lowestY(); y <= highestY(); y++) {
				result = result.concat("+---");
			}
			result = result.concat("+\n");
		}
		return result;
	}

	public static void main(String args[]) {
		Board b = new Board();
		b.boardAddMove(new Move(new Tile(Color.BLUE, Shape.STAR), new Coord(92, 92)));
		b.boardAddMove(new Move(new Tile(Color.GREEN, Shape.STAR), new Coord(92, 93)));
		System.out.println(b.toString());
	}
}