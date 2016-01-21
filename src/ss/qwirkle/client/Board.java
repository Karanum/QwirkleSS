package ss.qwirkle.client;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import ss.qwirkle.client.Move.MoveType;
import ss.qwirkle.client.tiles.Color;
import ss.qwirkle.client.tiles.Pattern;
import ss.qwirkle.client.tiles.Shape;
import ss.qwirkle.client.tiles.Tile;
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
	
	/** 
	 * Creates a new board.
	 */
	public Board() {
		board = new HashMap<Integer, Map<Integer, Tile>>();
	}
	
	public Board(Board b) {
		this.board = b.cloneBoard();
	}

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
	
	public boolean isEmpty() {
		return board.keySet().size() == 0;
	}
	
	/** 
	 * Makes a move on the Board.
	 * @param move The move that should be done
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
	
	public List<Tile> flattenBoard() {
		List<Tile> result = new ArrayList<Tile>();
		for (Integer y : board.keySet()) {
			Map<Integer, Tile> line = board.get(y);
			result.addAll(line.values());
		}
		return result;
	}
	
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
	
	private void placeTile(Tile tile) throws InvalidMoveException {
		int x = tile.getX();
		int y = tile.getY();
		if (!board.containsKey(y)) {
			board.put(y, new HashMap<Integer, Tile>());
		}
		board.get(y).put(x, tile);
		connectPatterns(tile, x, y);
	}
	
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
	//public Map<Integer, Map<Integer, Tile>> possibleTiles() {
	//	return null;
	//}
}
