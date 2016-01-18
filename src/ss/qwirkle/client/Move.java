package ss.qwirkle.client;

import java.util.HashMap;
import java.util.Map;

import ss.qwirkle.client.tiles.Tile;

/**
 * The move done by a player.
 * @author Dylan
 */
public class Move {
	//@ private invariant points >= 0;
	private int points;
	//@private invariant tiles != null;
	private Map<Integer, Map<Integer, Tile>> tiles;
	
	public Move() {
		tiles = new HashMap<Integer, Map<Integer, Tile>>();
		points = 0;
	}
	/**
	 * returns the rewarded points when doing this move.
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
