package ss.qwirkle.test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import ss.qwirkle.common.Move;
import ss.qwirkle.common.tiles.Color;
import ss.qwirkle.common.tiles.Shape;
import ss.qwirkle.common.tiles.ShapePattern;
import ss.qwirkle.common.tiles.Tile;

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
