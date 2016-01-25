package ss.qwirkle.common.tiles;

/**
 * The different colors that the tiles can have.
 * @author Dylan
 */
public enum Color {
	RED(0), ORANGE(1), YELLOW(2), GREEN(3), BLUE(4), PURPLE(5);
	
	private final int value;
	
	private Color(int value) {
		this.value = value;
	}
	
	/**
	 * Returns the integer value of the color.
	 */
	public int toInt() {
		return value;
	}
	
	public static Color fromInt(int id) {
		for (Color color : Color.values()) {
			if (color.toInt() == id) {
				return color;
			}
		}
		return null;
	}
}
