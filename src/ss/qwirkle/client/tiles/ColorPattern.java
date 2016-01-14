package ss.qwirkle.client.tiles;

import java.util.List;

/**
 * A type of Pattern consisting of colors.
 * @author Dylan
 */
public class ColorPattern implements Pattern {
	
	private List<Shape> shapes;
	
	/**
	 * Creates a CollorPattern object.
	 * It consists of tiles with the same color
	 * but different shapes.
	 */
	public ColorPattern(Color color) {
		
	}
	/**
	 * Returns if a pattern can merge.
	 */
	//@ requires pattern != null;
	@Override
	public boolean canMerge(Pattern pattern) {
		// TODO Auto-generated method stub
		return false;
	}
	/**
	 * Returns if a tile can be added to the pattern.
	 */
	//@ requires tile != null;
	@Override
	public boolean canAdd(Tile tile) {
		// TODO Auto-generated method stub
		return false;
	}
	/**
	 * Merges a ColorPattern with another ColorPattern.
	 * @param pattern the pattern to be merged.
	 */
	//@ requires pattern != null;	
	@Override
	public void merge(Pattern pattern) {
		// TODO Auto-generated method stub
		
	}
	/**
	 * Add a tile to ColorPattern.
	 */
	//@ requires tile != null;
	@Override
	public void add(Tile tile) {
		// TODO Auto-generated method stub
		
	}
	/**
	 * Returns the points rewarded with this pattern.
	 */
	@Override
	public int getPoints() {
		return 0;
		// TODO Auto-generated method stub
		
	}
	public List<Tile> getTiles() {
		return tiles;
	}
	

}
