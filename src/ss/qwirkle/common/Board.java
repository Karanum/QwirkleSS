package ss.qwirkle.common;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import ss.qwirkle.common.tiles.Pattern;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;
import ss.qwirkle.util.Range;

/**
 * The Qwirkle game board.
 * @author Dylan
 */
public class Board {
	
	//@ private invariant board != null;
	//@ private invariant (\forall Integer i; board.containsKey(i); board.get(i) != null);
	private Map<Integer, Map<Integer, Tile>> board;
	private Range xRange;
	private Range yRange;
	
	/** 
	 * Creates a new board.
	 */
	public Board() {
		board = new HashMap<Integer, Map<Integer, Tile>>();
		xRange = new Range(0, 0);
		yRange = new Range(0, 0);
	}
	
	/**
	 * Copies an existing board.
	 * @param b The board to copy
	 */
	//@ requires b != null;
	//@ ensures getXRange() != b.getXRange() && getYRange() != b.getYRange();
	//@ ensures (\forall int x, y; hasTile(x, y); getTile(x, y) != b.getTile(x, y));
	public Board(Board b) {
		board = b.cloneBoard();
		xRange = new Range(b.getXRange());
		yRange = new Range(b.getYRange());
	}

	/**
	 * Returns the tile at the specified location.
	 * @param x The x position of the tile
	 * @param y The y position of the tile
	 */
	//@ ensures hasTile(x, y) ==> \result.orElse(null) != null;
	//@ pure
	public Optional<Tile> getTile(int x, int y) {
		if (board.containsKey(y) && board.get(y).containsKey(x)) {
			return Optional.of(board.get(y).get(x));
		}
		return Optional.empty();
	}

	/**
	 * Returns whether a place on the board has a tile.
	 * @param x The x position to check
	 * @param y The y position to check
	 */
	//@ pure
	public boolean hasTile(int x, int y) {
		return board.containsKey(y) && board.get(y).containsKey(x);
	}
	
	/**
	 * Returns the horizontal range of the board.
	 */
	//@ pure
	public Range getXRange() {
		return xRange;
	}
	
	/**
	 * Returns the vertical range of the board.
	 */
	//@ pure
	public Range getYRange() {
		return yRange;
	}
	
	/**
	 * Returns whether the board contains no tiles.
	 */
	//@ pure
	public boolean isEmpty() {
		return board.keySet().isEmpty();
	}
	
	/**
	 * Places a move on the board.
	 * @param move The move to make
	 * @throws InvalidMoveException Throws this when the move is not allowed
	 */
	//@ requires move != null;
	public void doMove(Move move) throws InvalidMoveException {
		if (!BoardChecker.isMoveConnecting(this, move)) {
			throw new InvalidMoveException();
		}
		Board boardCopy = new Board(this);
		boardCopy.placeAllTiles(move.getTileCopies());
		placeAllTiles(move.getTiles());
	}
	
	/**
	 * Flattens the board into a one-dimensional collection of tiles.
	 */
	//@ ensures \result != null;
	//@ pure
	public List<Tile> flattenBoard() {
		List<Tile> result = new ArrayList<Tile>();
		for (Integer y : board.keySet()) {
			Map<Integer, Tile> line = board.get(y);
			result.addAll(line.values());
		}
		return result;
	}
	
	/**
	 * Makes a deep copy of the current board contents.
	 */
	//@ ensures \result != null;
	/*@ ensures (\forall int x, y; hasTile(x, y); 
					\result.containsKey(y) && \result.get(y).containsKey(x)); */
	//@ pure
	public Map<Integer, Map<Integer, Tile>> cloneBoard() {
		Map<Integer, Map<Integer, Tile>> copy = new HashMap<Integer, Map<Integer, Tile>>();
		for (Integer y : board.keySet()) {
			copy.put(y, new HashMap<Integer, Tile>());
			Map<Integer, Tile> line = board.get(y);
			for (Integer x : line.keySet()) {
				copy.get(y).put(x, new Tile(line.get(x), true));
			}
		}
		return copy;
	}
	
	/**
	 * Tries to place a tile on the board.
	 * @param tile The tile to place, should have proper x and y values
	 * @throws InvalidMoveException Throws this when the move is not allowed
	 */
	//@ requires tile != null;
	private void placeTile(Tile tile) throws InvalidMoveException {
		int x = tile.getX();
		int y = tile.getY();
		if (!board.containsKey(y)) {
			board.put(y, new HashMap<Integer, Tile>());
		}
		board.get(y).put(x, tile);
		xRange.setMinIfLess(x);
		xRange.setMaxIfMore(x);
		yRange.setMinIfLess(y);
		yRange.setMaxIfMore(y);
		connectPatterns(tile, x, y);
	}
	
	/**
	 * Places multiple tiles on the board.
	 * @param tiles The tiles to place, should have proper x and y values
	 * @throws InvalidMoveException Throws this when the move is not allowed
	 */
	//@ requires tiles != null && !tiles.isEmpty();
	private void placeAllTiles(List<Tile> tiles) throws InvalidMoveException {
		List<Tile> tilesCopy = new ArrayList<Tile>(tiles);
		do {
			boolean placedTile = false;
			for (int i = tilesCopy.size() - 1; i >= 0; --i) {
				Tile tile = tilesCopy.get(i);
				if (BoardChecker.canPlaceTile(this, tile, tile.getX(), tile.getY())) {
					placeTile(tile);
					placedTile = true;
					tilesCopy.remove(i);
				}
			}
			if (!placedTile) {
				throw new InvalidMoveException();
			}
		} while (tilesCopy.size() > 0);
	}
	
	/**
	 * Connects the patterns of a tile with its adjacent tiles.
	 * @param tile The tile to connect
	 * @param x The x position of the tile
	 * @param y The y position of the tile
	 * @throws InvalidMoveException Throws this when the move is not allowed
	 */
	//@ requires tile != null;
	private void connectPatterns(Tile tile, int x, int y) throws InvalidMoveException {
		Tile tileUp = getTile(x, y - 1).orElse(null);
		Tile tileDown = getTile(x, y + 1).orElse(null);
		Tile tileLeft = getTile(x - 1, y).orElse(null);
		Tile tileRight = getTile(x + 1, y).orElse(null);
		connectVertPattern(tile, tileUp);
		connectVertPattern(tile, tileDown);
		connectHorzPattern(tile, tileLeft);
		connectHorzPattern(tile, tileRight);
	}
	
	/**
	 * Connect the patterns of 2 tiles vertically.
	 * @param tile1 The first tile
	 * @param tile2 The second tile
	 * @throws InvalidMoveException Throws this when the move is not allowed
	 */
	private void connectVertPattern(Tile tile1, Tile tile2) throws InvalidMoveException {
		if (tile1 == null || tile2 == null) {
			return;
		}
		
		Pattern p1 = tile1.getVertPattern().orElse(null);
		Pattern p2 = tile2.getVertPattern().orElse(null);
		if (p1 == null) {
			if (p2 == null) {
				Pattern newPattern = tile1.makePatternWith(tile2).orElse(null);
				if (newPattern == null) {
					throw new InvalidMoveException();
				}
				tile1.setVertPattern(newPattern);
				tile2.setVertPattern(newPattern);
			} else {
				p2.add(tile1);
				tile1.setVertPattern(p2);
			}
		} else {
			if (p2 == null) {
				p1.add(tile2);
				tile2.setVertPattern(p2);
			} else if (p1 != p2) {
				p1.merge(p2);
			}
		}
	}
	
	/**
	 * Connect the patterns of 2 tiles horizontally.
	 * @param tile1 The first tile
	 * @param tile2 The second tile
	 * @throws InvalidMoveException Throws this when the move is not allowed
	 */
	private void connectHorzPattern(Tile tile1, Tile tile2) throws InvalidMoveException {
		if (tile1 == null || tile2 == null) {
			return;
		}
		
		Pattern p1 = tile1.getHorzPattern().orElse(null);
		Pattern p2 = tile2.getHorzPattern().orElse(null);
		if (p1 == null) {
			if (p2 == null) {
				Pattern newPattern = tile1.makePatternWith(tile2).orElse(null);
				if (newPattern == null) {
					throw new InvalidMoveException();
				}
				tile1.setHorzPattern(newPattern);
				tile2.setHorzPattern(newPattern);
			} else {
				p2.add(tile1);
				tile1.setHorzPattern(p2);
			}
		} else {
			if (p2 == null) {
				p1.add(tile2);
				tile2.setHorzPattern(p2);
			} else if (p1 != p2) {
				p1.merge(p2);
			}
		}
	}
}
