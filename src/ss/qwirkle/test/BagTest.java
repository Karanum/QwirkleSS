package ss.qwirkle.test;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import ss.qwirkle.client.Bag;
import ss.qwirkle.client.tiles.Color;
import ss.qwirkle.client.tiles.Shape;
import ss.qwirkle.client.tiles.Tile;

public class BagTest {

	Bag bag;
	int amount;
	
	@Before
	public void setUp() throws Exception {
		bag = new Bag();
		amount = Color.values().length * Shape.values().length * Bag.TILE_COPIES;
	}

	@Test
	public void testInitialAmount() {
		assertEquals(amount, bag.getSize());
	}
	
	@Test
	public void testGetTiles() {
		List<Tile> tiles = bag.getTiles(5);
		assertEquals(5, tiles.size());
		assertEquals(amount - 5, bag.getSize());
	}
	
	@Test
	public void testReturnTiles() {
		List<Tile> tiles = new ArrayList<Tile>();
		for (int i = 0; i < 4; ++i) {
			tiles.add(new Tile(Color.RED, Shape.CIRCLE));
		}
		bag.returnTiles(tiles);
		assertEquals(amount + 4, bag.getSize());
	}

}
