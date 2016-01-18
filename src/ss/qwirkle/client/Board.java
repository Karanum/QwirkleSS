package ss.qwirkle.client;

import java.util.HashMap;
import java.util.Map;

import ss.qwirkle.client.tiles.Tile;

/**
 * The board of the game Quirkle.
 * @author Dylan
 */
public class Board {
	
	//@ requires board != null;
	private Map<Integer, Map<Integer, Tile>> board;
	
	/** 
	 * creates a new board.
	 */
	public Board() {
		board = new HashMap<Integer, Map<Integer, Tile>>();
		
	}
	/** 
	 * makes a move on the Board.
	 * @param move the move you want to do.
	 */
	//@ requires move != null;
	public void doMove(Move move) {
		Map<Integer, Map<Integer, Tile>> boardCopy = new HashMap<Integer, Map<Integer, Tile>>();
		for (Integer key : board.keySet()) {
			Map<Integer, Tile> values = new HashMap<Integer, Tile>(board.get(key));
			boardCopy.put(key, values);
		}
		boolean running = true;
		Map<Integer, Map<Integer, Tile>> tiles = move.getTiles();
		for (Integer y : tiles.keySet()) {
			for (Integer x : tiles.get(y).keySet()) {
				if (hasTile(x, y)) {
					running = false;
				}
			}
		}
		if (!running) {
			return;
			
			//next check;
		}
		//if (boardCopy.)
		//if (!board.hasTile()) {
			
		//}
	}
	/**
	 * Returns if a place on the board has no tile.
	 * @param x the x position of the place.
	 * @param y the y position of the place.
	 */
	public boolean hasTile(int x, int y) {
		return board.containsKey(y) && board.get(y).containsKey(x);
	}
}
