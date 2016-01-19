package ss.qwirkle.client;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import ss.qwirkle.client.Move.MoveType;
import ss.qwirkle.client.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;

/**
 * The Qwirkle game board.
 * @author Dylan
 */
public class Board {
	
	//@ private invariant board != null;
	//@ private invariant (\forall Integer i; board.containsKey(i); board.get(i) != null);
	private Map<Integer, Map<Integer, Tile>> board;
	private Map<Integer, Map<Integer, Tile>> boardCopy;
	
	/** 
	 * Creates a new board.
	 */
	public Board() {
		board = new HashMap<Integer, Map<Integer, Tile>>();
	}

//	public boolean checkForFreePlace(Move move) {
//		Map<Integer, Map<Integer, Tile>> boardCopy = new HashMap<Integer, Map<Integer, Tile>>();
//		for (Integer key : board.keySet()) {
//			Map<Integer, Tile> values = new HashMap<Integer, Tile>(board.get(key));
//			boardCopy.put(key, values);
//		}
//		boolean result = true;
//		Map<Integer, Map<Integer, Tile>> tiles = move.getTiles();
//		for (Integer y : tiles.keySet()) {
//			for (Integer x : tiles.get(y).keySet()) {
//				if (hasTile(x, y)) {
//					result = false;
//				}
//			}
//		}
//		return result;
//	}
//	public boolean checkAddPattern(Move move) {
//		boolean result = false;
//		Map<Integer, Map<Integer, Tile>> tileList = move.getTiles();
//		for (Integer y : tileList.keySet()) {
//			Map<Integer, Tile> values = tileList.get(y);
//			for (Integer x : values.keySet()) {
//				Tile tile = values.get(x);
//				Tile above = getTile(x, y + 1);
//				Tile below = getTile(x, y - 1);
//				Tile left = getTile(x - 1, y);
//				Tile right = getTile(x + 1, y);
//				
//			}
//		}
//		return result;
//	}

	public Optional<Tile> getTile(int x, int y) {
		if (board.containsKey(y) && board.get(y).containsKey(x)) {
			return Optional.of(board.get(y).get(x));
		}
		return Optional.empty();
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
	
	/** 
	 * Makes a move on the Board.
	 * @param move The move that should be done
	 */
	//@ requires move != null;
	public void doMove(Move move) throws InvalidMoveException {
		boardCopy = cloneBoard();
		Map<Integer, Map<Integer, Tile>> tileMap = move.getTiles();
		List<Tile> tiles = placeAllTiles(tileMap);
		if (performPatternChecks(tiles, move.getType())) {
			//TODO: Finalize move
		}
	}
	
	public boolean canPlaceTile(Tile tile, int x, int y) {
		return false;
	}
	
	public List<Tile> flattenBoard() {
		List<Tile> result = new ArrayList<Tile>();
		for (Integer y : board.keySet()) {
			Map<Integer, Tile> line = board.get(y); 
			for (Integer x : line.keySet()) {
				result.add(line.get(x));
			}
		}
		return result;
	}
	
	private Map<Integer, Map<Integer, Tile>> cloneBoard() {
		Map<Integer, Map<Integer, Tile>> copy = new HashMap<Integer, Map<Integer, Tile>>();
		for (Integer key : board.keySet()) {
			copy.put(key, new HashMap<Integer, Tile>(board.get(key)));
		}
		return copy;
	}
	
	private void placeTile(Tile tile, int x, int y) {
		if (!board.containsKey(y)) {
			board.put(y, new HashMap<Integer, Tile>());
		}
		board.get(y).put(x, tile);
		tile.setX(x);
		tile.setY(y);
	}
	
	private List<Tile> placeAllTiles(Map<Integer, Map<Integer, Tile>> tiles)
			throws InvalidMoveException {
		List<Tile> result = new ArrayList<Tile>();
		for (Integer y : tiles.keySet()) {
			Map<Integer, Tile> line = tiles.get(y);
			for (Integer x : line.keySet()) {
				Tile tile = line.get(x);
				if (hasTile(x, y)) {
					throw new InvalidMoveException();
				}
				placeTile(tile, x, y);
				result.add(tile);
			}
		}
		return result;
	}
	
	private boolean performPatternChecks(List<Tile> tiles, MoveType moveType) {
		for (Tile tile : tiles) {
			
		}
		return false;
	}
	//public Map<Integer, Map<Integer, Tile>> possibleTiles() {
	//	return null;
	//}
}
