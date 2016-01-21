package ss.qwirkle.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.Before;
import org.junit.Test;

import ss.qwirkle.client.Board;
import ss.qwirkle.client.Move;
import ss.qwirkle.client.tiles.Color;
import ss.qwirkle.client.tiles.ColorPattern;
import ss.qwirkle.client.tiles.Pattern;
import ss.qwirkle.client.tiles.Shape;
import ss.qwirkle.client.tiles.Tile;
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
		m.addTile(new Tile(Color.YELLOW, Shape.DIAMOND), 0, 0);
		m.addTile(new Tile(Color.BLUE, Shape.DIAMOND), 1, 0);
		try {
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
		m.addTile(new Tile(Color.BLUE, Shape.CLOVER), 1, -1);
		m.addTile(new Tile(Color.BLUE, Shape.CROSS), 1, -2);
		try {
			b.doMove(m);
		} catch (InvalidMoveException e) {
			e.printStackTrace();
			fail();
		}
	}
	
	@Test 
	public void testInvalidStartingMove() {
		Move m = new Move();
		m.addTile(new Tile(Color.RED, Shape.CIRCLE), 2, 0);
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
		m.addTile(new Tile(Color.GREEN, Shape.DIAMOND), -1, 1);
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
		m1.addTile(new Tile(Color.YELLOW, Shape.STAR), 0, 0);
		m1.addTile(new Tile(Color.PURPLE, Shape.STAR), 1, 0);
		m2.addTile(new Tile(Color.PURPLE, Shape.CIRCLE), 1, 1);
		m3.addTile(new Tile(Color.PURPLE, Shape.CROSS), 1, 2);
		m3.addTile(new Tile(Color.YELLOW, Shape.CROSS), 0, 2);
		try {
			b.doMove(m1);
			b.doMove(m2);
			b.doMove(m3);
		} catch (InvalidMoveException e) {
			e.printStackTrace();
			fail();
		}
	}

}
