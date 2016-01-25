package ss.qwirkle.common.tiles;

import java.util.Optional;

/**
 * A single Qwirkle tile.
 * @author Dylan
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
	private int x;
	private int y;
	private int moveId;
	
	/**
	 * Creates a tile object.
	 * The object consists of a shape and a color.
	 * @param color The color of the tile
	 * @param shape The symbol on the tile
	 */
	//@ requires color != null;
	//@ requires shape != null;
	//@ ensures getColor() == color;
	//@ ensures getShape() == shape;
	public Tile(Color color, Shape shape) {
		this.color = color;
		this.shape = shape;
		vertPattern = null;
		horzPattern = null;
		x = 0;
		y = 0;
		moveId = -1;
	}
	
	/**
	 * Creates a tile object from its integer value.
	 * @param id The integer value of the tile
	 */
	//@ requires 0 <= id && id < Shape.values().length * Color.values().length;
	public Tile(int id) {
		this(Color.fromInt(id / 6), Shape.fromInt(id % 6));
	}
	
	/**
	 * Copies an existing Tile object.
	 * @param tile The tile to copy
	 * @param copyPatterns Whether to deep copy the patterns
	 */
	//@ requires tile != null;
	//@ ensures copyPatterns ==> getHorzPattern() != tile.getHorzPattern();
	//@ ensures copyPatterns ==> getVertPattern() != tile.getVertPattern();
	//@ ensures getColor() == tile.getColor() && getShape() == tile.getShape();
	//@ ensures getMoveId() == tile.getMoveId();
	public Tile(Tile tile, boolean copyPatterns) {
		color = tile.getColor();
		shape = tile.getShape();
		vertPattern = tile.getVertPattern().orElse(null);
		horzPattern = tile.getHorzPattern().orElse(null);
		if (copyPatterns) {
			if (vertPattern != null) {
				vertPattern = vertPattern.copy();
			}
			if (horzPattern != null) {
				horzPattern = horzPattern.copy();
			}
		}
		x = tile.getX();
		y = tile.getY();
		moveId = tile.getMoveId();
	}
	
	/**
	 * Return if a tile equals another tile.
	 * @param tile the tile to check.
	 */
	//@ requires tile != null;
	//@ ensures \result == (getColor() == tile.getColor() && getShape() == tile.getShape());
	//@ pure
	public boolean equals(Tile tile) {
		return tile.getShape() == shape && tile.getColor() == color;
	}
	
	/**
	 * Returns the ID of the move this tile belongs to, or -1 if the tile is not part of a move.
	 */
	//@ pure
	public int getMoveId() {
		return moveId;
	}
	
	/**
	 * Sets the move ID of this tile.
	 */
	//@ ensures getMoveId() == id;
	public void setMoveId(int id) {
		moveId = id;
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
	public Optional<Pattern> getHorzPattern() {
		return horzPattern == null ? Optional.<Pattern>empty() : Optional.<Pattern>of(horzPattern);
	}
	
	/**
	 * Returns the vertical pattern the tile is part of, or null.
	 */
	//@ pure
	public Optional<Pattern> getVertPattern() {
		return vertPattern == null ? Optional.<Pattern>empty() : Optional.<Pattern>of(vertPattern);
	}
	
	/**
	 * Sets the horizontal pattern of the tile.
	 * @param p The horizontal pattern
	 */
	//@ requires p != null;
	//@ ensures getHorzPattern().orElse(null) == p;
	public void setHorzPattern(Pattern p) {
		horzPattern = p;
	}
	
	/**
	 * Sets the vertical pattern of the tile.
	 * @param p The vertical pattern
	 */
	//@ requires p != null;
	//@ ensures getVertPattern().orElse(null) == p;
	public void setVertPattern(Pattern p) {
		vertPattern = p;
	}
	
	/**
	 * Returns the x position of the tile on the board.
	 * Will return a value even if the tile is not on the board, so this
	 * should not be used to check if the tile is part of the board.
	 */
	//@ pure
	public int getX() {
		return x;
	}
	
	/**
	 * Returns the y position of the tile on the board.
	 * Will return a value even if the tile is not on the board, so this
	 * should not be used to check if the tile is part of the board.
	 */
	//@ pure
	public int getY() {
		return y;
	}
	
	/**
	 * Sets the x position of the tile on the board.
	 * @param x The x position
	 */
	//@ ensures getX() == x;
	public void setX(int x) {
		this.x = x;
	}
	
	/**
	 * Sets the y position of the tile on the board.
	 * @param y The y position
	 */
	//@ ensures getY() == y;
	public void setY(int y) {
		this.y = y;
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
	 * @param tile The tile to compare with
	 */
	//@ requires tile != null;
	//@ ensures toInt() < tile.toInt() ==> \result < 0;
	//@ ensures toInt() == tile.toInt() ==> \result == 0;
	//@ ensures toInt() > tile.toInt() ==> \result > 0;
	//@ pure
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
	
	/**
	 * Checks for a common factor with another tile and returns a new Pattern
	 * containing both tiles based on this.
	 * @param tile The tile to form a pattern with
	 */
	public Optional<Pattern> makePatternWith(Tile tile) {
		Optional<Pattern> result = Optional.empty();
		if (color == tile.getColor() && shape != tile.getShape()) {
			ColorPattern p = new ColorPattern(color);
			p.add(tile);
			p.add(this);
			result = Optional.<Pattern>of(p);
		}
		if (shape == tile.getShape() && color != tile.getColor()) {
			ShapePattern p = new ShapePattern(shape);
			p.add(tile);
			p.add(this);
			result = Optional.<Pattern>of(p);
		}
		return result;
	}

}
