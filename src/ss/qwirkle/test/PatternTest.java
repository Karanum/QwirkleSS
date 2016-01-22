package ss.qwirkle.test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import ss.qwirkle.common.tiles.Color;
import ss.qwirkle.common.tiles.ColorPattern;
import ss.qwirkle.common.tiles.Shape;
import ss.qwirkle.common.tiles.ShapePattern;
import ss.qwirkle.common.tiles.Tile;

public class PatternTest {

	ShapePattern sPattern;
	ColorPattern cPattern;
	
	@Before
	public void setUp() throws Exception {
		sPattern = new ShapePattern(Shape.CIRCLE);
		cPattern = new ColorPattern(Color.BLUE);
	}

	@Test
	public void testShapeCanAdd() {
		Tile goodTile = new Tile(Color.ORANGE, Shape.CIRCLE);
		Tile badTile = new Tile(Color.ORANGE, Shape.CLOVER);
		assertTrue(sPattern.canAdd(goodTile));
		assertFalse(sPattern.canAdd(badTile));
		sPattern.add(goodTile);
		assertFalse(sPattern.canAdd(goodTile));
	}
	
	@Test
	public void testColorCanAdd() {
		Tile goodTile = new Tile(Color.BLUE, Shape.CROSS);
		Tile badTile = new Tile(Color.RED, Shape.CROSS);
		assertTrue(cPattern.canAdd(goodTile));
		assertFalse(cPattern.canAdd(badTile));
		cPattern.add(goodTile);
		assertFalse(cPattern.canAdd(goodTile));
	}
	
	@Test
	public void testShapeCanMerge() {
		ColorPattern badPattern = new ColorPattern(Color.BLUE);
		assertFalse(sPattern.canMerge(badPattern));
		
		ShapePattern pattern = new ShapePattern(Shape.SQUARE);
		assertFalse(sPattern.canMerge(pattern));
		
		pattern = new ShapePattern(Shape.CIRCLE);
		pattern.add(new Tile(Color.RED, Shape.CIRCLE));
		pattern.add(new Tile(Color.GREEN, Shape.CIRCLE));
		assertTrue(sPattern.canMerge(pattern));
		
		sPattern.add(new Tile(Color.RED, Shape.CIRCLE));
		assertFalse(sPattern.canMerge(pattern));
	}
	
	@Test
	public void testColorCanMerge() {
		ShapePattern badPattern = new ShapePattern(Shape.STAR);
		assertFalse(cPattern.canMerge(badPattern));
		
		ColorPattern pattern = new ColorPattern(Color.PURPLE);
		assertFalse(sPattern.canMerge(pattern));
		
		pattern = new ColorPattern(Color.BLUE);
		pattern.add(new Tile(Color.BLUE, Shape.CIRCLE));
		pattern.add(new Tile(Color.BLUE, Shape.SQUARE));
		assertTrue(cPattern.canMerge(pattern));
		
		cPattern.add(new Tile(Color.BLUE, Shape.CIRCLE));
		assertFalse(cPattern.canMerge(pattern));
	}

}
