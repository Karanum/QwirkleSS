package ss.qwirkle.client;

import java.util.HashMap;
import java.util.Map;

import ss.qwirkle.client.tiles.Tile;

/**
 * Object representing a move done by the player.
 * @author Dylan
 * 
 * TODO: Add checks for move validity when adding tiles
 */
public class Move {
	
	//@ private invariant points >= 0;
	//@private invariant tiles != null;
	private int points;
	private Map<Integer, Map<Integer, Tile>> tiles;
	
	public enum MoveType {
		VERTICAL, HORIZONTAL, SINGULAR;
	}
	
	/**
	 * Creates an empty move object.
	 */
	public Move() {
		tiles = new HashMap<Integer, Map<Integer, Tile>>();
		points = 0;
	}

	/**
	 * Returns the rewarded points for doing this move.
	 */
	public int getPoints() {
		return points;
	}
	
	public void addTile(Tile tile, int x, int y) {
		if (!tiles.containsKey(y)) {
			tiles.put(y, new HashMap<Integer, Tile>());
		}
		tiles.get(y).put(x, tile);
	}
	
	public Map<Integer, Map<Integer, Tile>> getTiles() {
		return tiles;
	}
	
	public MoveType getType() {
		if (tiles.size() == 0) {
			return MoveType.SINGULAR;
		}
		if (tiles.size() > 1) {
			return MoveType.VERTICAL;
		} else {
			Integer y = tiles.keySet().iterator().next();
			if (tiles.get(y).size() > 1) {
				return MoveType.HORIZONTAL;
			} else {
				return MoveType.SINGULAR;
			}
		}
	}

}
