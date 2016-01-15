package ss.qwirkle.client.tiles;

import java.util.ArrayList;
import java.util.List;

/**
 * A type of Pattern consisting of colors.
 * @author Dylan
 */
public class ColorPattern implements Pattern {
	
	private List<Shape> shapes;
	private Color color;
	private List<Tile> tiles;
	
	/**
	 * Creates a CollorPattern object.
	 * It consists of tiles with the same color
	 * but different shapes.
	 */
	public ColorPattern(Color color) {
		this.color = color;
		shapes = new ArrayList<Shape>();
		tiles = new ArrayList<Tile>();
	}
	public List<Shape> getShape() {
		return shapes;
	}
	/**
	 * Returns if a pattern can merge.
	 */
	//@ requires pattern != null;
	@Override
	public boolean canMerge(Pattern pattern) {
		boolean result = false;
		if (pattern instanceof ColorPattern) {
			result = true;
			List<Shape> otherShapes = ((ColorPattern) pattern).getShape();
			for (Shape shape : otherShapes) {
				result = result && !shapes.contains(shape);
			}
		}
		return result;
	}
	/**
	 * Returns if a tile can be added to the pattern.
	 */
	//@ requires tile != null;
	@Override
	public boolean canAdd(Tile tile) {
		return !shapes.contains(tile.getShape());

	}
	/**
	 * Merges a ColorPattern with another ColorPattern.
	 * @param pattern the pattern to be merged.
	 */
	//@ requires pattern != null;	
	@Override
	public void merge(Pattern pattern) {
		if (canMerge(pattern)) {
			List<Tile> otherTiles = pattern.getTiles();
			Pattern horzPattern = otherTiles.get(0).getHorzPattern();
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
	 * Add a tile to ColorPattern.
	 */
	//@ requires tile != null;
	@Override
	public void add(Tile tile) {
		tiles.add(tile);
		shapes.add(tile.getShape());
	}
	/**
	 * Returns the points rewarded with this pattern.
	 */
	@Override
	public int getPoints() {
		int points = shapes.size();
		if (shapes.size() == Shape.values().length) {
			points *= 2;
		}
		return points;
		
	}
	public List<Tile> getTiles() {
		return tiles;
	}
	

}
