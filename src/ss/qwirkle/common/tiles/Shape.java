package ss.qwirkle.common.tiles;

/**
 * The different shapes that the tiles can have.
 * @author Dylan
 */
public enum Shape {
	CIRCLE(0), CROSS(1), DIAMOND(2), SQUARE(3), STAR(4), CLOVER(5);
	
	private final int value;
	
	private Shape(int value) {
		this.value = value;
	}
	
	/**
	 * Returns the integer value of the shape.
	 */
	public int toInt() {
		return value;
	}
}
