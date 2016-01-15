package ss.qwirkle.client;

import java.util.Map;

import ss.qwirkle.client.tiles.Tile;

/**
 * The board of the game Quirkle.
 * @author Dylan
 */
public class Board {
	
	//@ requires board != null;
	private Map<Integer, Map <Integer, Tile>> board;
	
	/** 
	 * creates a new board.
	 */
	public Board() {
		
	}
	/** 
	 * makes a move on the Board.
	 * @param move the move you want to do.
	 */
	//@ requires move != null;
	public void doMove(Move move) {
		
	}
	/**
	 * Returns if a place on the board has no tile.
	 * @param x the x position of the place.
	 * @param y the y position of the place.
	 */
	public boolean isPlaceFree(int x, int y) {
		return false;
	}

}
