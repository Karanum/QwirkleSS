package ss.qwirkle.test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import ss.qwirkle.client.Move;
import ss.qwirkle.client.tiles.Color;
import ss.qwirkle.client.tiles.Shape;
import ss.qwirkle.client.tiles.ShapePattern;
import ss.qwirkle.client.tiles.Tile;

public class MoveTest {

	Move m;
	
	@Before
	public void setUp() throws Exception {
		m = new Move();
	}

	@Test
	public void testPatterns() {
		Tile t1 = new Tile(Color.GREEN, Shape.CLOVER);
		Tile t2 = new Tile(Color.GREEN, Shape.STAR);
		
		m.addTile(t1, 0, 0);
		assertEquals(null, t1.getHorzPattern().orElse(null));
		assertEquals(null, t1.getVertPattern().orElse(null));
		
		m.addTile(t2, 1, 0);
		assertEquals(t1.getHorzPattern().orElse(new ShapePattern(Shape.CLOVER)), 
						t2.getHorzPattern().orElse(new ShapePattern(Shape.STAR)));
		assertEquals(null, t1.getVertPattern().orElse(null));
		assertEquals(null, t2.getVertPattern().orElse(null));
	}

}
