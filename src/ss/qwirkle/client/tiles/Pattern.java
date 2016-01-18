package ss.qwirkle.client.tiles;

import java.util.List;

/**
 * The interface containing the pattern functionality.
 * @author Dylan
 */
public interface Pattern {
	
	/**
	 * returns if a patterns can merge.
	 * @param pattern the pattern to be merged.
	 */
	//@ requires pattern != null;
	public boolean canMerge(Pattern pattern);
	
	/**
	 * Returns if a tile can be added to the pattern.
	 * @param tile the tile to be added.
	 */
	//@ requires tile != null;
	public boolean canAdd(Tile tile);
	
	/**
	 * Merges a pattern with another pattern.
	 * @param pattern the pattern to be merged.
	 */
	//@ requires pattern != null;
	public void merge(Pattern pattern);
	
	/**
	 * Add a tile to the pattern.
	 */
	//@ requires tile != null;
	public void add(Tile tile);
	
	/**
	 * Returns the points rewarded with this pattern.
	 */
	public int getPoints();
	
	public List<Tile> getTiles();

}
