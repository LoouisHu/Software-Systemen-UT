package test;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import controller.TileBag;
import model.Tile;
import model.Tile.*;

public class BagTest {

	TileBag bag;
	int amount;
	
	@Before
	public void setUp() throws Exception {
		bag = new TileBag();
		amount = Tile.Color.values().length * Tile.Shape.values().length * 3;
	}

	@Test
	public void testInitialAmount() {
		assertEquals(amount, bag.getTileBagSize());
	}
	
	@Test
	public void testGetTiles() {
		List<Tile> tiles = bag.getTiles(7);
		System.out.println(bag.getTileBagSize());
		System.out.println(tiles.size());
		assertEquals(7, tiles.size());
		assertEquals(amount - 7, bag.getTileBagSize());
	}
	
	@Test
	public void testReturnTiles() {
		List<Tile> tiles = new ArrayList<Tile>();
		for (int i = 0; i < 4; ++i) {
			tiles.add(new Tile(Color.RED, Shape.CIRCLE));
		}
		bag.returnTiles(tiles);
		assertEquals(amount + 4, bag.getTileBagSize());
	}

}
