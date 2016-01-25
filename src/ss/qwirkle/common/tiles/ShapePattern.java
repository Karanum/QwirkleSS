package ss.qwirkle.common.tiles;

import java.util.ArrayList;
import java.util.List;

/**
 * A type of Pattern consisting of shapes.
 * @author Dylan
 */
public class ShapePattern implements Pattern {
	
	//@ private invariant colors != null;
	//@ private invariant shape != null;
	//@ private invariant tiles != null;
	private List<Color> colors;
	private Shape shape;
	private List<Tile> tiles;
	
	/**
	 * Creates a ShapePattern object.
	 * It consists of tiles with the same shape
	 * but different colors.
	 * @param shape The symbol of the pattern
	 */
	//@ requires shape != null;
	public ShapePattern(Shape shape) {
		this.shape = shape;
		colors = new ArrayList<Color>();
		tiles = new ArrayList<Tile>();
	}
	
	/**
	 * Makes a copy of the pattern and all its tiles.
	 */
	//@ ensures \result.getShape() == getShape();
	//@ ensures \result.getColors().containsAll(getColors());
	@Override
	public ShapePattern copy() {
		ShapePattern copy = new ShapePattern(shape);
		for (Tile tile : tiles) {
			copy.add(new Tile(tile, false));
		}
		return copy;
	}
	
	/**
	 * Returns the list of colors currently present in the pattern.
	 */
	//@ pure
	public List<Color> getColors() {
		return colors;
	}
	
	/**
	 * Returns whether a pattern can merged into this pattern.
	 * @param pattern The pattern to check
	 */
	//@ requires pattern != null;
	//@ ensures pattern instanceof ShapePattern ==> !\result;
	@Override
	public boolean canMerge(Pattern pattern) {
		boolean result = false;
		if (tiles.size() + pattern.getTiles().size() <= 6) {
			if (pattern instanceof ShapePattern) {
				ShapePattern sPattern = (ShapePattern) pattern;
				if (sPattern.getShape() == shape) {
					result = true;
					List<Color> otherColors = ((ShapePattern) pattern).getColors();
					for (Color color : otherColors) {
						result = result && !colors.contains(color);
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
	//@ ensures \result == !getColors().contains(tile.getColor()) && tile.getShape() == getShape();
	@Override
	public boolean canAdd(Tile tile) {
		return !colors.contains(tile.getColor()) && tile.getShape() == shape;
	}
	
	/**
	 * Merges a ShapePattern with another ShapePattern.
	 * @param pattern The pattern to be merged.
	 */
	//@ requires pattern != null;
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
	 * Add a tile to a ShapePattern.
	 * @param tile The tile to be added
	 */
	//@ requires tile != null;
	//@ ensures canAdd(tile) ==> getTiles().contains(tile);
	//@ ensures canAdd(tile) ==> getColors().contains(tile.getColor());
	@Override
	public void add(Tile tile) {
		if (canAdd(tile)) {
			tiles.add(tile);
			colors.add(tile.getColor());
		}
	}
	
	/**
	 * Returns the points rewarded with this pattern.
	 */
	//@ pure
	@Override
	public int getPoints() {
		int points = colors.size();
		if (colors.size() == Color.values().length) {
			points *= 2;
		}
		return points;
	}
	
	/**
	 * Returns the list of tiles included in this pattern.
	 */
	//@ pure
	public List<Tile> getTiles() {
		return tiles;
	}
	
	/**
	 * Returns the shape shared by all tiles in this pattern.
	 */
	//@ pure
	public Shape getShape() {
		return shape;
	}

}
