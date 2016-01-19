package ss.qwirkle.client.tiles;

import java.util.ArrayList;
import java.util.List;

/**
 * A type of Pattern consisting of shapes.
 * @author Dylan
 */
public class ShapePattern implements Pattern {
	
	//TODO: Needs to have its JML updated once finished
	
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
	 * @param Shape The symbol of the pattern
	 */
	//@ requires shape != null;
	public ShapePattern(Shape shape) {
		this.shape = shape;
		colors = new ArrayList<Color>();
		tiles = new ArrayList<Tile>();
	}
	
	/**
	 * Returns the list of colors currently present in the pattern.
	 */
	//@ pure
	public List<Color> getColors() {
		return colors;
	}
	
	/**
	 * Returns if a pattern can merge.
	 */
	//@ requires pattern != null;
	//@ ensures pattern instanceof ShapePattern ==> !\result;
	@Override
	public boolean canMerge(Pattern pattern) {
		boolean result = false;
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
		return result;
	}
	
	/**
	 * Returns if a tile can be added to the pattern.
	 */
	//@ requires tile != null;
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
	 * Add a tile to a ShapePattern.
	 */
	//@ requires tile != null;
	@Override
	public void add(Tile tile) {
		tiles.add(tile);
		colors.add(tile.getColor());
		
	}
	
	/**
	 * Returns the points rewarded with this pattern.
	 */
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
	public Shape getShape() {
		return shape;
	}

}
