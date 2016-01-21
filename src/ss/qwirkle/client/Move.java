package ss.qwirkle.client;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import ss.qwirkle.client.tiles.Color;
import ss.qwirkle.client.tiles.ColorPattern;
import ss.qwirkle.client.tiles.Pattern;
import ss.qwirkle.client.tiles.Shape;
import ss.qwirkle.client.tiles.ShapePattern;
import ss.qwirkle.client.tiles.Tile;
import ss.qwirkle.util.Range;

/**
 * Object representing a move done by the player.
 * @author Dylan
 */
public class Move {
	
	private static int nextId = 0;
	
	//@ private invariant points >= 0;
	//@private invariant tiles != null;
	private int points;
	private List<Tile> tiles;
	private MoveType type;
	private Range xRange;
	private Range yRange;
	private int id;
	
	public enum MoveType {
		VERTICAL, HORIZONTAL, SINGULAR;
	}
	
	/**
	 * Creates an empty move object.
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
	public int getPoints() {
		return points;
	}
	
	public void addTile(Tile tile, int x, int y) {
		if (applyMove(tile, x, y)) {
			tile.setX(x);
			tile.setY(y);
			tile.setMoveId(id);
			tiles.add(tile);
			xRange.setMinIfLess(x);
			xRange.setMaxIfMore(x);
			yRange.setMinIfLess(y);
			yRange.setMaxIfMore(y);
		}
	}
	
	public List<Tile> getTiles() {
		return tiles;
	}
	
	public List<Tile> getTileCopies() {
		List<Tile> result = new ArrayList<Tile>();
		for (Tile t : tiles) {
			result.add(new Tile(t, true));
		}
		return result;
	}
	
	public Optional<Tile> getTile(int x, int y) {
		Optional<Tile> result = Optional.empty();
		for (Tile tile : tiles) {
			if (tile.getX() == x && tile.getY() == y) {
				result = Optional.of(tile);
			}
		}
		return result;
	}
	
	public MoveType getType() {
		return type;
	}
	
	public Range getXRange() {
		return xRange;
	}
	
	public Range getYRange() {
		return yRange;
	}
	
	private boolean applyMove(Tile tile, int x, int y) {
		if (!tiles.isEmpty()) {
			if (type == MoveType.SINGULAR) {
				return applyMoveSingular(tile, x, y);
			} else if (type == MoveType.VERTICAL) {
				int moveY = yRange.getMin();
				Tile prevTile = tiles.get(0);
				Pattern p = prevTile.getVertPattern().orElse(null);
				if (y != moveY || !p.canAdd(tile)) {
					return false;
				}
				p.add(tile);
			} else {
				int moveX = xRange.getMin();
				Tile prevTile = tiles.get(0);
				Pattern p = prevTile.getHorzPattern().orElse(null);
				if (x != moveX || !p.canAdd(tile)) {
					return false;
				}
				p.add(tile);
			}
		}
		return true;
	}
	
	private boolean applyMoveSingular(Tile tile, int x, int y) {
		Tile prevTile = tiles.get(0);
		int prevX = prevTile.getX();
		int prevY = prevTile.getY();
		
		Pattern p = null;
		Color prevColor = prevTile.getColor();
		Shape prevShape = prevTile.getShape();
		if (tile.getColor() == prevColor) {
			if (tile.getShape() == prevShape) {
				return false;
			}
			p = new ColorPattern(prevColor);
		} else if (tile.getShape() == prevShape) {
			p = new ShapePattern(prevShape);
		} else {
			return false;
		}
		
		if (prevY != y && prevX != x) {
			return false;
		}
		
		p.add(prevTile);
		p.add(tile);
		if (prevX == x) {
			type = MoveType.VERTICAL;
			prevTile.setVertPattern(p);
			tile.setVertPattern(p);
		} else {
			type = MoveType.HORIZONTAL;
			prevTile.setHorzPattern(p);
			tile.setHorzPattern(p);
		}
		return true;
	}

}
