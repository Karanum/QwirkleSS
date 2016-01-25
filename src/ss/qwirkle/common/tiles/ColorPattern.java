package ss.qwirkle.common.tiles;

import java.util.ArrayList;
import java.util.List;

/**
 * A type of Pattern consisting of colors.
 * @author Dylan
 */
public class ColorPattern implements Pattern {
	
	//@ private invariant shapes != null;
	//@ private invariant color != null;
	//@ private invariant tiles != null;
	private List<Shape> shapes;
	private Color color;
	private List<Tile> tiles;
	
	/**
	 * Creates a CollorPattern object.
	 * It consists of tiles with the same color
	 * but different shapes.
	 * @param color The color of the pattern
	 */
	//@ requires color != null;
	//@ ensures getColor() == color;
	public ColorPattern(Color color) {
		this.color = color;
		shapes = new ArrayList<Shape>();
		tiles = new ArrayList<Tile>();
	}
	
	/**
	 * Makes a copy of the pattern and all its tiles.
	 */
	//@ ensures \result.getColor() == getColor();
	//@ ensures \result.getShapes().containsAll(getShapes());
	public ColorPattern copy() {
		ColorPattern copy = new ColorPattern(color);
		for (Tile tile : tiles) {
			copy.add(new Tile(tile, false));
		}
		return copy;
	}
	
	/**
	 * Returns the list of shapes currently present in the pattern.
	 */
	//@ pure
	public List<Shape> getShapes() {
		return shapes;
	}

	/**
	 * Returns the color shared by all tiles in the pattern.
	 */
	//@ pure
	public Color getColor() {
		return color;
	}

	/**
	 * Returns whether a pattern can merge into this pattern.
	 * @param pattern The pattern to check
	 */
	//@ requires pattern != null;
	//@ pure
	@Override
	public boolean canMerge(Pattern pattern) {
		boolean result = false;
		if (tiles.size() + pattern.getTiles().size() <= 6) {
			if (pattern instanceof ColorPattern) {
				ColorPattern cPattern = (ColorPattern) pattern;
				if (cPattern.getColor() == color) {
					result = true;
					List<Shape> otherShapes = cPattern.getShapes();
					for (Shape shape : otherShapes) {
						result = result && !shapes.contains(shape);
					}
				}
			}
		}
		return result;
	}
	
	/**
	 * Returns whether a tile can be added to the pattern.
	 * @param tile The tile to check
	 */
	//@ requires tile != null;
	//@ pure
	@Override
	public boolean canAdd(Tile tile) {
		return !shapes.contains(tile.getShape()) && tile.getColor() == color;

	}
	
	/**
	 * Merges the pattern with another ColorPattern.
	 * @param pattern The pattern to be merged
	 */
	//@ requires pattern != null;
	/*@ ensures canMerge(pattern) ==> getTiles().size() == 
									\old(getTiles().size()) + pattern.getTiles().size(); */
	@Override
	public void merge(Pattern pattern) {
		if (canMerge(pattern)) {
			List<Tile> otherTiles = pattern.getTiles();
			Pattern horzPattern = otherTiles.get(0).getHorzPattern().orElse(null);
			boolean isHorz = false;
			if (horzPattern != null && horzPattern.equals(pattern)) {
				isHorz = true;
			}
			for (Tile tile : otherTiles) {
				add(tile);
				if (isHorz) {
					tile.setHorzPattern(this);
				} else {
					tile.setVertPattern(this);
				}
			}
		}
		
	}
	
	/**
	 * Adds a tile to the pattern.
	 * @param tile The tile to be added
	 */
	//@ requires tile != null;
	//@ ensures canAdd(tile) ==> getTiles().contains(tile);
	//@ ensures canAdd(tile) ==> getShapes().contains(tile.getShape());
	@Override
	public void add(Tile tile) {
		if (canAdd(tile)) {
			tiles.add(tile);
			shapes.add(tile.getShape());
		}
	}
	
	/**
	 * Returns the points rewarded by this pattern.
	 */
	//@ pure
	@Override
	public int getPoints() {
		int points = shapes.size();
		if (shapes.size() == Shape.values().length) {
			points *= 2;
		}
		return points;
		
	}
	
	/**
	 * Returns the list of tiles contained by this pattern.
	 */
	//@ pure
	public List<Tile> getTiles() {
		return tiles;
	}
	

}
