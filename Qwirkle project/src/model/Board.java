package model;

import java.util.ArrayList;
import java.util.List;

import model.Tile.Color;
import model.Tile.Shape;

public class Board {

	public static Tile[][] boardSpaces;
	public static final int DIM = 183;
	public static final int POVERMOVELENGTH = 6;

	/**
	 * Maakt in de constructor een tweedimensionale bord van de Tile klasse, met
	 * DIM als lengte.
	 */
	/*
	 * @public invariant boardSpaces.length == DIM;
	 * 
	 * @ensures (\forall int i; 0 <= i & i < DIM * DIM; this.getField(i) ==
	 * null);
	 */
	public Board() {
		boardSpaces = new Tile[DIM][DIM];
	}

	/**
	 * Kijkt of een zet geldig is volgens de regels van Qwirkle.
	 * 
	 * @param move
	 * @return true als de andere validMove true is;
	 */
	/*@ requires move.getXCoor() < DIM;
		requires move.getYCoor() < DIM;
 	ensures this.inLineV(move) && 
 			this.inLineX(move) ==> \result == true;*/
	/* @pure */
	public boolean validMove(Move move) {
		return validMove(move, new ArrayList<Move>());
	}

	/**
	 * Kijkt of een zet geldig is volgens de regels van Qwirkle.
	 * 
	 * @param theMove
	 * @param movesMade
	 * @return
	 */
	/*@ requires move.getXCoor() < DIM;
	requires move.getYCoor() < DIM;
	ensures this.inLineV(move) && 
			this.inLineX(move) ==> \result == true;*/
	/* @pure */
	public boolean validMove(Move theMove, List<Move> movesMade) {
		boolean firstMove = boardSpaces[91][91] == null;
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
	 * 
	 * @param m
	 *            de move die je maakt.
	 * @return true als de zet mogelijk is.
	 */

	/*@ requires c.getY() < DIM;
 	requires x < DIM;
	ensures ((\forall int i; 
 					(\forall int j; 0 <= j & j < i; boardSpaces[y - j][x] != null); 
 			(boardSpaces[y - i][x].getColor() == t.getColor() && 
 				!(boardSpaces[y - i][x].getShape() == t.getShape())) || 
 			(boardSpaces[y - i][x].getShape() == t.getShape() && 
 				!(boardSpaces[y - i][x].getColor() == t.getColor())) ||
 			i == y) &&
 				(\forall int i; 
 					(\forall int j; 0 <= j & j < i; boardSpaces[y + i][x] != null); 
 			(boardSpaces[y + i][x].getColor() == t.getColor() && 
 				!(boardSpaces[y + i][x].getShape() == t.getShape())) || 
 			(boardSpaces[y + i][x].getShape() == t.getShape() && 
 				!(boardSpaces[y + i][x].getColor() == t.getColor())) ||
 			i == y)) ==> \result == true;
	/* @pure */
	public boolean inLineV(Move m) {
		Coord c = m.getCoord();
		Tile t = m.getTile();
		ArrayList<Tile> tiles = new ArrayList<Tile>();
		int x = c.getX();
		int y = c.getY();

		for (int i = 1; i < POVERMOVELENGTH; i++) {
			Tile tit = boardSpaces[x][y + i];
			if (tit == null) {
				break;
			}
			tiles.add(tit);
		}
		for (int i = 1; i < POVERMOVELENGTH; i++) {
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
	 * 
	 * @param m
	 *            de move die je maakt.
	 * @return true als de zet mogelijk is.
	 */
	/*@ requires y < DIM;
		requires x < DIM;
		ensures ((\forall int i; 
					(\forall int j; 0 <= j & j < i; boardSpaces[y][x - j] != null); 
			(boardSpaces[y][x - i].getColor() == c.getColor() && 
				!(boardSpaces[y][x - i].getShape() == c.getShape())) || 
			(boardSpaces[y][x - i].getShape() == c.getShape() && 
				!(boardSpaces[y][x - i].getColor() == c.getColor())) ||
			i == x) &&
				(\forall int i; 
					(\forall int j; 0 <= j & j < i; boardSpaces[y][x + j] != null); 
			(boardSpaces[y][x + i].getColor() == c.getColor() && 
				!(boardSpaces[y][x + i].getShape() == c.getShape())) || 
			(boardSpaces[y][x + i].getShape() == c.getShape() && 
				!(boardSpaces[y][x + i].getColor() == c.getColor())) ||
			i == x)) ==> \result == true;
	/* @pure */
	public boolean inLineH(Move m) {
		Coord c = m.getCoord();
		Tile t = m.getTile();
		ArrayList<Tile> tiles = new ArrayList<Tile>();
		int x = c.getX();
		int y = c.getY();

		for (int i = 1; i < POVERMOVELENGTH; i++) {
			Tile tit = boardSpaces[x + i][y];
			if (tit == null) {
				break;
			}
			tiles.add(tit);
		}
		for (int i = 1; i < POVERMOVELENGTH; i++) {
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

	/*
	 * @requires 0 <= x & x <= DIM;
	 * 
	 * @requires 0 <= y & y<= DIM;
	 */
	/* @pure */public Tile getField(int x, int y) {
		return boardSpaces[x][y];
	}

	/**
	 * Voegt een Tile toe op de x en y coördinaat van boardSpaces.
	 * 
	 * @param move
	 */
	/*
	 * @requires move.getCoord().getX() < DIM;
	 * 
	 * @requires move.getCoord().getX() < DIM;
	 * 
	 * @ensures \result == move.getTile();
	 * 
	 */
	public void boardAddMove(Move move) {
		boardSpaces[move.getCoord().getX()][move.getCoord().getY()] = move.getTile();
	}

	/**
	 * Verwijdert e en Tile van de x en y coördinaat van boardSpaces.
	 * 
	 * @param coord
	 */
	/*
	 * @requires coord != null;
	 * @ensures \result == boardSpaces[null][null];
	 */
	public void boardRemove(Coord coord) {
		boardSpaces[coord.getX()][coord.getY()] = null;
	}

	/**
	 * Keert een lijst terug van boardSpaces waar een zet is op gedaan.
	 * 
	 * @return
	 */

	/* @pure */public List<Move> getUsedSpaces() {
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
		int y = 91;
		while (!this.emptyYRow(y)) {
			y--;
		}
		return y;
	}

	/* @ ensures \result < DIM; */
	/* @pure */
	public int highestY() {
		int y = 91;
		while (!this.emptyYRow(y)) {
			y++;
		}
		return y;
	}

	/**
	 * Telkens als je een Tile op het bord zet, krijg je punten bij je
	 * score opgeteld. Het puntensysteem gaat als volgt: als je een tile 
	 * in een rij legt van tiles, dan krijg je het aantal punten equivalent aan het 
	 * aantal tiles in de rij. Als je tile grenst aan nog een rij met
	 * tiles, dan krijg je het aantal punten equivalent aan de lengte van
	 * die rij, inclusief de tile die beide rijen kruisen, dus die tile
	 * telt dan twee keer.
	 * 
	 * Als je 6 stenen achter elkaar legt, heb je Qwirkle en krijg je 6
	 * punten plus 6 extra punten voor het maken van een Qwirkle.
	 * @param moves
	 * @return
	 */
	/*@ requires p.getXCoor() < DIM;
	requires p.getYCoor() < DIM;
 	requires isValidMove(p);*/
	public int decideScore(List<Move> moves) {
		int result = 0;
		int x = 0;
		int y = 0;
		if (moves.size() != 0) {
			x = moves.get(0).getCoord().getX();
			y = moves.get(0).getCoord().getY();
		}
		for (int i = 0; i < moves.size(); i++) {
			int currentX = moves.get(i).getCoord().getX();
			int currentY = moves.get(i).getCoord().getY();
			boolean north = true;
			boolean south = true;
			boolean west = true;
			boolean east = true;
			int horizontal = 1;
			int vertical = 1;
			for (int j = 1; j < POVERMOVELENGTH; j++) {

				if (boardSpaces[currentX - j][currentY] != null && west) {
					horizontal++;
				} else {
					west = false;
				}
				if (boardSpaces[currentX + j][currentY] != null && east) {
					horizontal++;
				} else {
					east = false;
				}
				if (boardSpaces[currentX][currentY - j] != null && south) {
					vertical++;
				} else {
					south = false;
				}
				if (boardSpaces[currentX][currentY + j] != null && north) {
					vertical++;
				} else {
					north = false;
				}
			}
			if (horizontal == 1 && vertical == 1) {
				result = 1;
			} else if (vertical > 1) {
				if (i == 0 || x != currentX) {
					result = result + vertical;
				}
			} else if (horizontal > 1) {
				if (i == 0 || y != currentY) {
					result = result + horizontal;
				}
			}
			if (horizontal == POVERMOVELENGTH && (i == 0 || y != currentY)) {
				result += POVERMOVELENGTH;
			}
			if (vertical == POVERMOVELENGTH && (i == 0 || x != currentX)) {
				result += POVERMOVELENGTH;
			}

		}
		return result;
	}

	/**
	 * Maakt een Textual Interface van een board. Aan de boven- en linkerrand
	 * staan de coördinaten van de rij en kolom. Als er in een rij of kolom geen
	 * enkele tile is gezet, dan wordt die rij niet geprint. Het board is
	 * dynamisch.
	 */

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

	public static void main(String[] args) {
		Board b = new Board();
		b.boardAddMove(new Move(new Tile(Color.BLUE, Shape.STAR), new Coord(91, 91)));
		b.boardAddMove(new Move(new Tile(Color.GREEN, Shape.STAR), new Coord(91, 92))); 
		System.out.println(b.toString());
	}
}