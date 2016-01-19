package ss.qwirkle.client;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import ss.qwirkle.client.Move.MoveType;
import ss.qwirkle.client.tiles.Pattern;
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
		Integer minPos = null;
		Integer maxPos = null;
		for (Tile tile : tiles) {
			if (!performPatternCheck(tile)) {
				return false;
			}
			if (moveType == MoveType.HORIZONTAL) {
				if (minPos == null || minPos > tile.getX()) {
					minPos = tile.getX();
				}
				if (maxPos == null || maxPos < tile.getX()) {
					maxPos = tile.getX();
				}
			} else if (moveType == MoveType.VERTICAL) {
				if (minPos == null || minPos > tile.getY()) {
					minPos = tile.getY();
				}
				if (maxPos == null || maxPos < tile.getY()) {
					maxPos = tile.getY();
				}
			}
		}
		
		if (moveType == MoveType.HORIZONTAL) {
			Tile tileLeft = getTile(minPos - 1, tiles.get(0).getY()).orElse(null);
			Tile tileRight = getTile(maxPos + 1, tiles.get(0).getY()).orElse(null);
			Pattern patternLeft = 
							tileLeft != null ? tileLeft.getHorzPattern().orElse(null) : null;
			Pattern patternRight =
							tileRight != null ? tileRight.getHorzPattern().orElse(null) : null;
		}
		return true;
	}
	
	private boolean performPatternCheck(Tile tile) {
		int x = tile.getX();
		int y = tile.getY();
		Tile tileUp = getTile(x, y - 1).orElse(null);
		Tile tileDown = getTile(x, y + 1).orElse(null);
		Tile tileLeft = getTile(x - 1, y).orElse(null);
		Tile tileRight = getTile(x + 1, y).orElse(null);
		
		if (tileUp != null || tileDown != null) {
			Pattern patternUp =
							tileUp != null ? tileUp.getVertPattern().orElse(null) : null;
			Pattern patternDown =
							tileDown != null ? tileDown.getVertPattern().orElse(null) : null;
			if (!checkPatterns(patternUp, patternDown, tileUp, tileDown, tile)) {
				return false;
			}
		}
		if (tileLeft != null || tileRight != null) {
			Pattern patternLeft =
							tileLeft != null ? tileLeft.getHorzPattern().orElse(null) : null;
			Pattern patternRight =
							tileRight != null ? tileRight.getHorzPattern().orElse(null) : null;
			if (!checkPatterns(patternLeft, patternRight, tileLeft, tileRight, tile)) {
				return false;
			}
		}
		return false;
	}
	
	private boolean checkPatterns(Pattern p1, Pattern p2, Tile tile1, Tile tile2, Tile self) {
		if (p1 != null && p2 != null && !p1.canMerge(p2)) {
			return false;
		}
		if (p1 != null) {
			if (p2 == null && tile2 != null && !p1.canAdd(tile2)) {
				return false;
			}
			if (!p1.canAdd(self)) {
				return false;
			}
		}
		if (p2 != null) {
			if (p1 == null && tile1 != null && !p2.canAdd(tile1)) {
				return false;
			}
			if (!p2.canAdd(self)) {
				return false;
			}
		}
		return true;
	}
}
