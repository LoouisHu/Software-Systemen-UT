package test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import model.Tile;
import model.Tile.Color;
import model.Tile.Shape;
public class TileTest {

	Tile tile;
	
	@Before
	public void setUp() throws Exception {
		tile = new Tile(Color.RED, Shape.CROSS);
	}

	@Test
	public void testGetters() {
		assertEquals(tile.getColor(), Color.RED);
		assertEquals(tile.getShape(), Shape.CROSS);
	}
	
	@Test
	public void testEquals() {
		Tile tile2 = new Tile(Color.GREEN, Shape.CROSS);
		Tile tile3 = new Tile(Color.RED, Shape.CROSS);
		Tile tile4 = new Tile(Color.RED, Shape.DIAMOND);
		assertFalse(tile.equals(tile2));
		assertTrue(tile.getShape().equals(tile3.getShape()));
		assertTrue(tile.getColor().equals(tile3.getColor()));
		assertFalse(tile.equals(tile4));
	}

}