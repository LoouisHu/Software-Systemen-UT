package test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;
import static org.junit.Assert.assertFalse;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import model.Board;
import model.Coord;
import model.Move;
import model.Tile;
import model.Tile.Color;
import model.Tile.Shape;

public class BoardTest {

	private Board b;

	@Before
	public void setUp() {
		b = new Board();
	}

	@Test
	public void testCorrectFirstMove() {
		Tile t = new Tile(Color.BLUE, Shape.STAR);
		Coord c = new Coord(92, 92);
		Move m = new Move(t, c);
		// System.out.println(m.toString());
		b.boardAddMove(m);
		b.toString();
	}

	@Test
	public void testMultipleMoves() {
		Tile t1 = new Tile(Color.GREEN, Shape.CIRCLE);
		Tile t2 = new Tile(Color.ORANGE, Shape.CIRCLE);
		b.boardAddMove(new Move(new Tile(Color.BLUE, Shape.CIRCLE), new Coord(91, 91)));
		b.boardAddMove(new Move(new Tile(Color.GREEN, Shape.CIRCLE), new Coord(91, 92)));
		b.boardAddMove(new Move(new Tile(Color.ORANGE, Shape.CIRCLE), new Coord(91, 93)));
		b.boardAddMove(new Move(new Tile(Color.YELLOW, Shape.CROSS), new Coord(91, 94)));
		assertEquals(t1.getColor(), b.getField(91, 92).getColor());
		assertEquals(t2.getShape(), b.getField(91, 93).getShape());
		assertFalse(b.validMove(new Move(new Tile(Color.YELLOW, Shape.CROSS), new Coord(91, 94))));
	}

	@Test
	public void longerThanSixAndScore() {
		Move m1 = new Move(new Tile(Color.BLUE, Shape.CIRCLE), new Coord(92, 92));
		Move m2 = new Move(new Tile(Color.GREEN, Shape.CIRCLE), new Coord(92, 93));
		Move m3 = new Move(new Tile(Color.ORANGE, Shape.CIRCLE), new Coord(92, 94));
		Move m4 = new Move(new Tile(Color.PURPLE, Shape.CIRCLE), new Coord(92, 95));
		Move m5 = new Move(new Tile(Color.RED, Shape.CIRCLE), new Coord(92, 96));
		Move m6 = new Move(new Tile(Color.YELLOW, Shape.CIRCLE), new Coord(92, 97));
		Move m7 = new Move(new Tile(Color.GREEN, Shape.CIRCLE), new Coord(92, 98));
		b.boardAddMove(m1); 
		b.boardAddMove(m2); 
		b.boardAddMove(m3); 
		b.boardAddMove(m4); 
		b.boardAddMove(m5); 
		b.boardAddMove(m6); 
		b.boardAddMove(m7); 
		List<Move> moves = new ArrayList<Move>();
		moves.add(m1);
		moves.add(m2);
		moves.add(m3);
		moves.add(m4);
		moves.add(m5);
		moves.add(m6);
		moves.add(m7);
		b.decideScore(moves);
	//	System.out.println(b.decideScore(moves));
	//	System.out.println(b.getField(92, 92));
		Tile t1 = new Tile(Color.BLUE, Shape.CIRCLE);
	//	System.out.println(t1);
		assertEquals(b.getField(92, 92).getColor(), t1.getColor());
		assertEquals(b.getField(92, 92).getShape(), t1.getShape());
		assertFalse(b.validMove(new Move(new Tile(Color.GREEN, Shape.CIRCLE), new Coord(92, 98))));
		assertEquals(b.decideScore(moves), 12);
	}

	@Test
	public void testEmptyRow() {
		assertTrue(b.emptyXRow(42));
		assertTrue(b.emptyYRow(90));
		b.boardAddMove(new Move(new Tile(Color.PURPLE, Shape.SQUARE), new Coord(50, 46)));
		assertFalse(b.emptyXRow(50));
		assertFalse(b.emptyYRow(46));
	}

}
