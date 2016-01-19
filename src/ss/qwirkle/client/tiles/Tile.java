package ss.qwirkle.client.tiles;

/**
 * @author Dylan
 * 
 */
public class Tile {
	
	//@ private invariant vertPattern != null;
	//@ private invariant horzPattern != null;
	private Pattern vertPattern;
	private Pattern horzPattern;
	private Color color;
	private Shape shape;
	
	/**
	 * Creates a tile object.
	 * The object consists of a shape and a color.
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
	public boolean equals(Tile tile) {
		return tile.getShape() == shape && tile.getColor() == color;
	}
	public Color getColor() {
		return color;
	}
	public Shape getShape() {
		return shape;
	}
	public Pattern getHorzPattern() {
		return horzPattern;
	}
	public Pattern getVertPattern() {
		return vertPattern;
	}
	
	public void setHorzPattern(Pattern p) {
		horzPattern = p;
	}
	
	public void setVertPattern(Pattern p) {
		vertPattern = p;
	}

}
