package Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.HashSet;

import org.junit.Before;
import org.junit.Test;

import Qwirkle.Board;
import Qwirkle.Coord;
import Qwirkle.Move;
import Qwirkle.Tile;
import Qwirkle.Tile.Color;
import Qwirkle.Tile.Shape;
import player.HumanPlayer;
import player.Player;

public class BoardTest {
	
	private Board board;
	
	@Before
	public void setUp(){
		board = new Board();
	}
	
	@Test
	public void TestMove(){
		Tile t = new Tile(Color.BLUE, Shape.DIAMOND);
		Coord c = new Coord(2, 5);
		Move m = new Move(t, c);
		board.boardAddMove(m);
		assertEquals(board.boardSpaces[2][5], t);
		assertEquals(board.boardSpaces[2][4], null);
	}
	
	@Test
	public void isValidMove(){
		Tile t1 = new Tile(Color.BLUE, Shape.CIRCLE);
		Tile t2 = new Tile(Color.BLUE, Shape.CLOVER);
		Tile t3 = new Tile(Color.GREEN, Shape.SQUARE);
		HashSet<Tile> tiless = new HashSet<>();
		tiless.add(t1);
		tiless.add(t2);
		tiless.add(t3);
		Coord c1 = new Coord(0, 0);
		Coord c2 = new Coord(1, 0);
		Coord c3 = new Coord(2, 0);
		Player louis = new HumanPlayer("louis", tiless);
		louis.makeMove(t1, c1);
		louis.makeMove(t2, c2);
		louis.makeMove(t3, c3);
		assertTrue(board.boardSpaces[0][0] == t1);
		assertTrue(board.boardSpaces[1][0] == t2);
		assertFalse(board.boardSpaces[2][0] == t3);
	}
}
