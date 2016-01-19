package ss.qwirkle.client.tiles;

/**
 * @author Dylan
 * 
 */
public class Tile implements Comparable<Tile> {
	
	//@ private invariant vertPattern != null;
	//@ private invariant horzPattern != null;
	//@ private invariant color != null;
	//@ private invariant shape != null;
	private Pattern vertPattern;
	private Pattern horzPattern;
	private Color color;
	private Shape shape;
	
	/**
	 * Creates a tile object.
	 * The object consists of a shape and a color.
	 * @param color The color of the tile
	 * @param shape The symbol on the tile
	 */
	//@ requires color != null;
	//@ requires shape != null;
	public Tile(Color color, Shape shape) {
		this.color = color;
		this.shape = shape;
		vertPattern = null;
		horzPattern = null;
	}
	
	/**
	 * Return if a tile equals another tile.
	 * @param tile the tile to check.
	 */
	//@ requires tile != null;
	//@ ensures \result == (getColor() == tile.getColor() && getShape() == tile.getShape());
	//@ pure
	public boolean equals(Tile tile) {
		return false;
	}
	
	/**
	 * Returns the color of the tile.
	 */
	//@ pure
	public Color getColor() {
		return color;
	}
	
	/**
	 * Returns the symbol of the tile.
	 */
	//@ pure
	public Shape getShape() {
		return shape;
	}
	
	/**
	 * Returns the horizontal pattern the tile is part of, or null.
	 */
	//@ pure
	public Pattern getHorzPattern() {
		return horzPattern;
	}
	
	/**
	 * Returns the vertical pattern the tile is part of, or null.
	 */
	//@ pure
	public Pattern getVertPattern() {
		return vertPattern;
	}
	
	/**
	 * Sets the horizontal pattern of the tile.
	 * @param p The horizontal pattern
	 */
	//@ requires p != null;
	//@ ensures getHorzPattern() == p;
	public void setHorzPattern(Pattern p) {
		horzPattern = p;
	}
	
	/**
	 * Sets the vertical pattern of the tile.
	 * @param p The vertical pattern
	 */
	//@ requires p != null;
	//@ ensures getVertPattern() == p;
	public void setVertPattern(Pattern p) {
		vertPattern = p;
	}
	
	/**
	 * Converts the tile to an integer for sorting or communication purposes.
	 */
	//@ pure
	public int toInt() {
		return color.toInt() * 6 + shape.toInt();
	}

	/**
	 * Compares the tile with another tile based on their integer values.
	 */
	@Override
	public int compareTo(Tile tile) {
		int ownValue = toInt();
		int otherValue = tile.toInt();
		if (ownValue < otherValue) {
			return -1;
		} else if (ownValue > otherValue) {
			return 1;
		} else {
			return 0;
		}
	}

}
