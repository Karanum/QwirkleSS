package ss.qwirkle.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import org.junit.Before;
import org.junit.Test;

import ss.qwirkle.common.Board;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.tiles.Color;
import ss.qwirkle.common.tiles.Shape;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;

public class MoveTest {

	Move m;
	Board b;
	
	@Before
	public void setUp() throws Exception {
		m = new Move();
		b = new Board();
	}

	@Test
	public void testPatterns() {
		Tile t1 = new Tile(Color.GREEN, Shape.CLOVER);
		Tile t2 = new Tile(Color.GREEN, Shape.STAR);
		
		try {
			m.addTile(b, t1, 0, 0);
			assertEquals(null, t1.getHorzPattern().orElse(null));
			assertEquals(null, t1.getVertPattern().orElse(null));
			
			m.addTile(b, t2, 1, 0);
			assertEquals(null, t1.getVertPattern().orElse(null));
			assertEquals(null, t2.getVertPattern().orElse(null));
		} catch (InvalidMoveException e) {
			fail();
		}
	}

}
