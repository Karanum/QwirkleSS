package ss.qwirkle.test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import ss.qwirkle.client.tiles.Color;
import ss.qwirkle.client.tiles.Shape;
import ss.qwirkle.client.tiles.Tile;

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
		assertTrue(tile.equals(tile3));
		assertFalse(tile.equals(tile4));
	}

}
