package model;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import model.Tile.Color;
import model.Tile.Shape;

public class Board {

	public static Tile[][] boardSpaces;
	public static final int DIM = 183;
	public static final int powerMoveLength = 6;

	/**
	 * Maakt in de constructor een tweedimensionale bord van de Tile klasse, met DIM als lengte.
	 */
	/*
	 * @public invariant boardSpaces.length == DIM;
	 * @ensures (\forall int i; 0 <= i & i < DIM * DIM; this.getField(i) == null);
	 */
	public Board() {
		boardSpaces = new Tile[DIM][DIM];
	}	

	/**
	 * Kijkt of een zet geldig is volgens de regels van Qwirkle.
	 * @param move
	 * @return true als de andere validMove true is;
	 */
	
	/*@pure*/
	public boolean validMove(Move move) {
		return validMove(move, new ArrayList<Move>());
	}

	/**
	 * Kijkt of een zet geldig is volgens de regels van Qwirkle.
	 * @param theMove
	 * @param movesMade
	 * @return
	 */
	//TODO jml
	/*@pure*/
	public boolean validMove(Move theMove, List<Move> movesMade) {
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
	/**
	 * Checkt op de verticale as of de move geldig is bij één tile.
	 * @param m 
	 * 			de move die je maakt.
	 * @return true als de zet mogelijk is.
	 */
	
	//TODO JML
	/*@pure*/
	public boolean inLineV(Move m) {
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
		boolean shapeRelation = t.getShape() == tiles.get(0).getShape();
		boolean colorRelation = t.getColor() == tiles.get(0).getColor();
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
	 * Checkt op de horizontale as of de move geldig is bij één tile.
	 * @param m 
	 * 			de move die je maakt.
	 * @return true als de zet mogelijk is.
	 */
	//TODO jml
	/*@pure*/
	public boolean inLineH(Move m) {
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
		boolean shapeRelation = t.getShape() == tiles.get(0).getShape();
		boolean colorRelation = t.getColor() == tiles.get(0).getColor();
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
	 * Laat zien of een veld leeg is.
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
	 * Geeft true als een rij helemaal leeg is.
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
	 * Geeft true als een kolom helemaal leeg is.
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
	/* @requires 0 <= x & x <= DIM;
	 * @requires 0 <= y & y<= DIM;
	 */
	/*@pure*/public Tile getField(int x, int y) {
		return boardSpaces[x][y];
	}
	
	/**
	 * Voegt een Tile toe op de x en y coördinaat van boardSpaces.
	 * @param move
	 */
	/* @requires move.getCoord().getX() < DIM;
	 * @requires move.getCoord().getX() < DIM;
	 * @ensures \result == move.getTile();
	 * 
	 */
	public void boardAddMove(Move move) {
		boardSpaces[move.getCoord().getX()][move.getCoord().getY()] = move.getTile();
	}

	/**
	 * Verwijdert e en Tile van de x en y coördinaat van boardSpaces.
	 * @param coord
	 */
	public void boardRemove(Coord coord) {
		boardSpaces[coord.getX()][coord.getY()] = null;
	}
	/**
	 * Keert een lijst terug van boardSpaces waar een zet is op gedaan.
	 * @return
	 */
	
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
	/* @pure */
	public int lowestX() {
		int x = 92;
		while (!this.emptyXRow(x)) {
			x--;
		}
		return x;
	}

	/* @ ensures \result < DIM; */
	/* @pure */
	public int highestX() {
		int x = 92;
		while (!this.emptyXRow(x)) {
			x++;
		}
		return x;
	}

	/* @ ensures \result < DIM; */
	/* @pure */
	public int lowestY() {
		int y = 92;
		while (!this.emptyYRow(y)) {
			y--;
		}
		return y;
	}

	/* @ ensures \result < DIM; */
	/* @pure */
	public int highestY() {
		int y = 92;
		while (!this.emptyYRow(y)) {
			y++;
		}
		return y;
	}
	/**
	 * Maakt een Textual Interface van een board.
	 * Aan de boven- en linkerrand staan de coördinaten van de rij en kolom.
	 * Als er in een rij of kolom geen enkele tile is gezet, 
	 * dan wordt die rij niet geprint. Het board is dynamisch.
	 */
	/*@pure*/
	public String toString() {
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

}