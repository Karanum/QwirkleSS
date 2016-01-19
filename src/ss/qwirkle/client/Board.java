package ss.qwirkle.client;

import java.util.HashMap;
import java.util.Map;

import ss.qwirkle.client.tiles.Tile;

/**
 * The Qwirkle game board.
 * @author Dylan
 */
public class Board {
	
	//@ private invariant board != null;
	//@ private invariant (\forall Integer i; board.containsKey(i); board.get(i) != null);
	private Map<Integer, Map<Integer, Tile>> board;
	
	/** 
	 * Creates a new board.
	 */
	public Board() {
		board = new HashMap<Integer, Map<Integer, Tile>>();
	}
	
	/** 
	 * Makes a move on the Board.
	 * @param move The move that should be done
	 */
	//TODO finish function
	//@ requires move != null;
	public void doMove(Move move) {
		if (checkForFreePlace(move) && checkAddPattern(move)) {
			//do move;
		}
	}

	public boolean checkForFreePlace(Move move) {
		Map<Integer, Map<Integer, Tile>> boardCopy = new HashMap<Integer, Map<Integer, Tile>>();
		for (Integer key : board.keySet()) {
			Map<Integer, Tile> values = new HashMap<Integer, Tile>(board.get(key));
			boardCopy.put(key, values);
		}
		boolean result = true;
		Map<Integer, Map<Integer, Tile>> tiles = move.getTiles();
		for (Integer y : tiles.keySet()) {
			for (Integer x : tiles.get(y).keySet()) {
				if (hasTile(x, y)) {
					result = false;
				}
			}
		}
		return result;
	}
	//TODO finish function
	public boolean checkAddPattern(Move move) {
		boolean result = false;
		Map<Integer, Map<Integer, Tile>> tileList = move.getTiles();
		for (Integer y : tileList.keySet()) {
			Map<Integer, Tile> values = tileList.get(y);
			for (Integer x : values.keySet()) {
				Tile tile = values.get(x);
				Tile above = getTile(x, y + 1);
				Tile below = getTile(x, y - 1);
				Tile left = getTile(x - 1, y);
				Tile right = getTile(x + 1, y);
				
			}
		}
		return result;
	}

	public Tile getTile(int x, int y) {
		Tile tile = null;
		if (board.containsKey(y) && board.get(y).containsKey(x)) {
			tile = board.get(y).get(x);
		}
		return tile;
	}

	/**
	 * Returns if a place on the board has no tile.
	 * @param x The x position to check
	 * @param y The y position to check
	 */
	//@ pure
	public boolean hasTile(int x, int y) {
		return board.containsKey(y) && board.get(y).containsKey(x);
	}
	
	public boolean canPlaceTile(Tile tile, int x, int y) {
		return false;
	}
	//public Map<Integer, Map<Integer, Tile>> possibleTiles() {
	//	return null;
	//}
}
