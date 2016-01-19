package ss.qwirkle.client;

import java.util.HashMap;
import java.util.Map;

import ss.qwirkle.client.tiles.Tile;

/**
 * Object representing a move done by the player.
 * @author Dylan
 */
public class Move {
	
	//@ private invariant points >= 0;
	//@private invariant tiles != null;
	private int points;
	private Map<Integer, Map<Integer, Tile>> tiles;
	
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

}
