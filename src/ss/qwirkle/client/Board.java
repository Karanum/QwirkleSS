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
	//@ requires move != null;
	public void doMove(Move move) {
		
	}
	
	/**
	 * Returns if a place on the board has no tile.
	 * @param x The x position to check
	 * @param y The y position to check
	 */
	//@ pure;
	public boolean isPlaceFree(int x, int y) {
		return false;
	}

}
