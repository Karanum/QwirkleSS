package ss.qwirkle.common;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import ss.qwirkle.common.tiles.Color;
import ss.qwirkle.common.tiles.ColorPattern;
import ss.qwirkle.common.tiles.Pattern;
import ss.qwirkle.common.tiles.Shape;
import ss.qwirkle.common.tiles.ShapePattern;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;
import ss.qwirkle.util.Range;

/**
 * Object representing a move done by the player.
 * @author Dylan
 */
public class Move {
	
	private static int nextId = 0;
	
	//@ private invariant points >= 0;
	//@ private invariant tiles != null;
	//@ private invariant type != null;
	//@ private invariant xRange != null;
	//@ private invariant yRange != null;
	private int points;
	private List<Tile> tiles;
	private MoveType type;
	private Range xRange;
	private Range yRange;
	private Pattern pattern;
	private int id;
	
	public enum MoveType {
		VERTICAL, HORIZONTAL, SINGULAR;
	}
	
	/**
	 * Creates an empty move object and assigns it a move id.
	 */
	public Move() {
		tiles = new ArrayList<Tile>();
		points = 0;
		type = MoveType.SINGULAR;
		
		xRange = new Range();
		yRange = new Range();
		
		id = nextId;
		++nextId;
	}

	/**
	 * Returns the rewarded points for doing this move.
	 */
	//@ pure
	public int getPoints() {
		//TODO: Implement proper point calculations :c
		return points;
	}
	
	/**
	 * Adds a tile to the move.
	 * @param b The board instance of the game.
	 * @param tile The tile to be added
	 * @param x The x coordinate of the tile
	 * @param y The y coordinate of the tile
	 * @throws InvalidMoveException Throws this when the move is not allowed
	 */
	//@ requires b != null && tile != null;
	public void addTile(Board b, Tile tile, int x, int y) throws InvalidMoveException {
		if (applyMove(b, tile, x, y)) {
			tile.setX(x);
			tile.setY(y);
			tile.setMoveId(id);
			tiles.add(tile);
			xRange.setMinIfLess(x);
			xRange.setMaxIfMore(x);
			yRange.setMinIfLess(y);
			yRange.setMaxIfMore(y);
		} else {
			throw new InvalidMoveException();
		}
	}
	
	/**
	 * Returns the list of tiles contained in the move.
	 */
	//@ pure
	public List<Tile> getTiles() {
		return tiles;
	}
	
	/**
	 * Returns deep copies of all tiles contained in the move.
	 */
	//@ pure
	public List<Tile> getTileCopies() {
		List<Tile> result = new ArrayList<Tile>();
		for (Tile t : tiles) {
			result.add(new Tile(t, true));
		}
		return result;
	}
	
	/**
	 * Returns a tile from the move if it exists.
	 * @param x The x coordinate of the tile
	 * @param y The y coordinate of the tile
	 */
	//@ ensures hasTile(x, y) ==> \result != null;
	//@ pure
	public Optional<Tile> getTile(int x, int y) {
		Optional<Tile> result = Optional.empty();
		for (Tile tile : tiles) {
			if (tile.getX() == x && tile.getY() == y) {
				result = Optional.of(tile);
			}
		}
		return result;
	}
	
	/**
	 * Returns whether there is a tile at the specified position in the move.
	 * @param x The x coordinate
	 * @param y The y coordinate
	 * @return
	 */
	//@ pure
	public boolean hasTile(int x, int y) {
		for (Tile tile : tiles) {
			if (tile.getX() == x && tile.getY() == y) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * Returns the type of the move.
	 */
	//@ pure
	public MoveType getType() {
		return type;
	}
	
	/**
	 * Returns the horizontal range of the move.
	 */
	//@ pure
	public Range getXRange() {
		return xRange;
	}
	
	/**
	 * Returns the vertical range of the move.
	 */
	//@ pure
	public Range getYRange() {
		return yRange;
	}
	
	/**
	 * Prepares a tile to be added to the move.
	 * @param b The board instance of this game
	 * @param tile The tile to be added
	 * @param x The x coordinate of the tile
	 * @param y The y coordinate of the tile
	 * @return Success value
	 */
	//@ requires b != null && tile != null;
	private boolean applyMove(Board b, Tile tile, int x, int y) {
		if (!BoardChecker.canPlaceTile(b, tile, x, y, false) || hasTile(x, y)) {
			return false;
		}
		if (!tiles.isEmpty()) {
			if (type == MoveType.SINGULAR) {
				return applyMoveSingular(tile, x, y);
			} else if (type == MoveType.VERTICAL) {
				int moveX = xRange.getMin();
				if (x != moveX || !pattern.canAdd(tile)) {
					return false;
				}
				pattern.add(tile);
			} else {
				int moveY = yRange.getMin();
				if (y != moveY || !pattern.canAdd(tile)) {
					return false;
				}
				pattern.add(tile);
			}
		}
		return true;
	}
	
	/**
	 * Prepares a tile to be added to the move if the move is singular.
	 * @param tile The tile to be added
	 * @param x The x coordinate of the tile
	 * @param y The y coordinate of the tile
	 * @return Success value
	 */
	//@ requires tile != null;
	private boolean applyMoveSingular(Tile tile, int x, int y) {
		Tile prevTile = tiles.get(0);
		int prevX = prevTile.getX();
		int prevY = prevTile.getY();
		
		Color prevColor = prevTile.getColor();
		Shape prevShape = prevTile.getShape();
		if (tile.getColor() == prevColor) {
			if (tile.getShape() == prevShape) {
				return false;
			}
			pattern = new ColorPattern(prevColor);
		} else if (tile.getShape() == prevShape) {
			pattern = new ShapePattern(prevShape);
		} else {
			return false;
		}
		
		if (prevY != y && prevX != x) {
			return false;
		}
		
		pattern.add(prevTile);
		pattern.add(tile);
		type = prevX == x ? MoveType.VERTICAL : MoveType.HORIZONTAL;
		return true;
	}

}
