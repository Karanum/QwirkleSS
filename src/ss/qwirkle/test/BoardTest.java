package ss.qwirkle.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.Before;
import org.junit.Test;

import ss.qwirkle.common.Board;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.tiles.Color;
import ss.qwirkle.common.tiles.Shape;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;

public class BoardTest {

	Board b;
	
	@Before
	public void setUp() throws Exception {
		b = new Board();
	}
	
	@Test
	public void testCorrectStartingMove() {
		Move m = new Move();
		try {
			m.addTile(b, new Tile(Color.YELLOW, Shape.DIAMOND), 0, 0);
			m.addTile(b, new Tile(Color.BLUE, Shape.DIAMOND), 1, 0);
			assertEquals(2, m.getTiles().size());
			b.doMove(m);
		} catch (InvalidMoveException e) {
			e.printStackTrace();
			fail();
		}
		assertTrue(b.hasTile(0, 0));
		assertTrue(b.hasTile(1, 0));
		assertEquals(m.getTile(0, 0).orElse(null).getHorzPattern().orElse(null), 
						m.getTile(1, 0).orElse(null).getHorzPattern().orElse(null));
		assertEquals(null, m.getTile(0, 0).orElse(null).getVertPattern().orElse(null));
		assertEquals(null, m.getTile(1, 0).orElse(null).getVertPattern().orElse(null));
	}
	
	@Test
	public void testCorrectMove() {
		testCorrectStartingMove();
		
		Move m = new Move();
		try {
			m.addTile(b, new Tile(Color.BLUE, Shape.CLOVER), 1, -1);
			m.addTile(b, new Tile(Color.BLUE, Shape.CROSS), 1, -2);
			assertEquals(2, m.getTiles().size());
			b.doMove(m);
		} catch (InvalidMoveException e) {
			e.printStackTrace();
			fail();
		}
	}
	
	@Test 
	public void testInvalidStartingMove() {
		Move m = new Move();
		try {
			m.addTile(b, new Tile(Color.RED, Shape.CIRCLE), 2, 0);
		} catch (InvalidMoveException e) {
			fail();
		}
		assertEquals(1, m.getTiles().size());
		
		try {
			b.doMove(m);
			fail();
		} catch (InvalidMoveException e) {
		}
	}
	
	@Test
	public void testInvalidPositionedMove() {
		testCorrectStartingMove();
		
		Move m = new Move();
		try {
			m.addTile(b, new Tile(Color.GREEN, Shape.DIAMOND), -1, 1);
		} catch (InvalidMoveException e) {
			fail();
		}
		assertEquals(1, m.getTiles().size());
		
		try {
			b.doMove(m);
			fail();
		} catch (InvalidMoveException e) {
		}
	}
	
	@Test
	public void testDisconnectedMove() {
		Move m1 = new Move();
		Move m2 = new Move();
		Move m3 = new Move();
		try {
			m1.addTile(b, new Tile(Color.YELLOW, Shape.STAR), 0, 0);
			m1.addTile(b, new Tile(Color.PURPLE, Shape.STAR), 1, 0);
			m2.addTile(b, new Tile(Color.PURPLE, Shape.CIRCLE), 1, 1);
			m3.addTile(b, new Tile(Color.PURPLE, Shape.CROSS), 1, 2);
			m3.addTile(b, new Tile(Color.YELLOW, Shape.CROSS), 0, 2);
			assertEquals(2, m1.getTiles().size());
			assertEquals(1, m2.getTiles().size());
			assertEquals(2, m3.getTiles().size());
		} catch (InvalidMoveException e) {
			fail();
		}
		try {
			b.doMove(m1);
			b.doMove(m2);
			b.doMove(m3);
		} catch (InvalidMoveException e) {
			e.printStackTrace();
			fail();
		}
		
		Move m4 = new Move();
		try {
			m4.addTile(b, new Tile(Color.YELLOW, Shape.DIAMOND), 0, -1);
			m4.addTile(b, new Tile(Color.YELLOW, Shape.SQUARE), 0, 3);
		} catch (InvalidMoveException e) {
			fail();
		}
		assertEquals(2, m4.getTiles().size());
		
		try {
			b.doMove(m4);
			fail();
		} catch (InvalidMoveException e) {
		}
		
		try {
			m4.addTile(b, new Tile(Color.YELLOW, Shape.CIRCLE), 0, 1);
			assertEquals(3, m4.getTiles().size());
			b.doMove(m4);
		} catch (InvalidMoveException e) {
			e.printStackTrace();
			fail();
		}
	}

}
