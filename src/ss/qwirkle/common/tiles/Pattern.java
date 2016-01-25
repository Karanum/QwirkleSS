package ss.qwirkle.common.tiles;

import java.util.List;

/**
 * The interface containing the pattern functionality.
 * @author Dylan
 */
public interface Pattern {
	
	/**
	 * Makes a copy of the pattern and all its tiles.
	 */
	//@ ensures \result.getPoints() == getPoints();
	/*@ ensures (\forall int i; 0 < i && i < getTiles().size();
						getTiles().get(i).equals(\result.getTiles().get(i))); */
	public Pattern copy();
	
	/**
	 * Returns if the pattern can merge with another pattern.
	 * @param pattern The pattern to be merged
	 */
	//@ requires pattern != null;
	//@ pure
	public boolean canMerge(Pattern pattern);
	
	/**
	 * Returns if a tile can be added to the pattern.
	 * @param tile The tile to be added
	 */
	//@ requires tile != null;
	//@ pure
	public boolean canAdd(Tile tile);
	
	/**
	 * Merges the pattern with another pattern.
	 * @param pattern The pattern to be merged
	 */
	//@ requires pattern != null;
	public void merge(Pattern pattern);
	
	/**
	 * Adds a tile to the pattern.
	 * @param tile The tile to be added
	 */
	//@ requires tile != null;
	public void add(Tile tile);
	
	/**
	 * Returns the points rewarded with this pattern.
	 */
	//@ pure
	public int getPoints();
	
	/**
	 * Returns the list of tiles contained in this pattern.
	 */
	//@ pure
	public List<Tile> getTiles();

}
