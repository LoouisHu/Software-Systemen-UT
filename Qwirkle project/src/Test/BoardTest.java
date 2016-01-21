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
		Coord c1 = new Coord(91, 91);
		Coord c2 = new Coord(92, 91);
		Coord c3 = new Coord(93, 91);
		Player louis = new HumanPlayer("louis", tiless);
		louis.makeMove(t1, c1);
		louis.makeMove(t2, c2);
		louis.makeMove(t3, c3);
		assertTrue(board.boardSpaces[91][91] == t1);
		System.out.println("Joepie ik kom hier!");
		System.out.println(t2.toString());
		System.out.println(board.boardSpaces[92][91].toString());
		//System.out.println(board.boardSpaces[92][91].getColor() + board.boardSpaces[92][91].getShape());
		assertTrue(board.boardSpaces[92][91] == t2);
		assertFalse(board.boardSpaces[93][91] == t3);
	}
}
