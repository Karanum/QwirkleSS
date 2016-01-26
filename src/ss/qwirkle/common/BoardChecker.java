package ss.qwirkle.common;

import java.util.List;

import ss.qwirkle.common.tiles.Pattern;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.util.Range;

/**
 * Auxiliary class for checking the validity of moves on the board.
 * @author Karanum
 */
public abstract class BoardChecker {

	/**
	 * Returns whether a tile can be placed on the board.
	 * @param board The board instance to place the tile on
	 * @param tile The tile to the placed
	 * @param x The x coordinate of the tile
	 * @param y The y coordinate of the tile
	 * @param checkAttached Whether to check if the tile is attached to any other tiles
	 */
	//@ requires board != null;
	//@ requires tile != null;
	//@ ensures board.isEmpty() && x == 0 && y == 0 ==> \result;
	//@ ensures board.hasTile(x, y) ==> !\result;
	//@ ensures checkAttached && !isCoordAttached(board, x, y) ==> !\result;
	//@ pure
	public static boolean canPlaceTile(Board board, Tile tile, int x, int y, 
										boolean checkAttached) {
		if (board.isEmpty()) {
			if (x == 0 && y == 0) {
				return true;
			}
		}
		if (board.hasTile(x, y)) {
			return false;
		}
		if (checkAttached && !isCoordAttached(board, x, y)) {
			return false;
		}
		return canConnectPatterns(board, tile, x, y);
	}
	
	/**
	 * Returns whether a tile can be placed on the board. Checks if it is connected.
	 * @param board The board instance to place the tile on
	 * @param tile The tile to the placed
	 * @param x The x coordinate of the tile
	 * @param y The y coordinate of the tile
	 */
	//@ requires board != null;
	//@ requires tile != null;
	//@ ensures \result == canPlaceTile(board, tile, x, y, true);
	//@ pure
	public static boolean canPlaceTile(Board board, Tile tile, int x, int y) {
		return canPlaceTile(board, tile, x, y, true);
	}
	
	/**
	 * Returns whether the position on the board has any tiles next to it.
	 * @param board The board instance to check this on
	 * @param x The x coordinate
	 * @param y The y coordinate
	 */
	//@ requires board != null;
	//@ pure
	public static boolean isCoordAttached(Board board, int x, int y) {
		Tile tileUp = board.getTile(x, y - 1).orElse(null);
		Tile tileDown = board.getTile(x, y + 1).orElse(null);
		Tile tileLeft = board.getTile(x - 1, y).orElse(null);
		Tile tileRight = board.getTile(x + 1, y).orElse(null);
		return tileUp != null || tileDown != null || tileLeft != null || tileRight != null;
	}
	
	/**
	 * Returns whether a move is connected. (That is, no empty tiles in between)
	 * @param board The board instance to check this on
	 * @param move The move to be checked
	 */
	//@ requires board != null && move != null;
	//@ pure
	public static boolean isMoveConnecting(Board board, Move move) {
		Range xRange = move.getXRange();
		Range yRange = move.getYRange();
		for (int y : yRange.forEach()) {
			for (int x : xRange.forEach()) {
				Tile moveTile = move.getTile(x, y).orElse(null);
				if (moveTile == null && !board.hasTile(x, y)) {
					return false;
				}
			}
		}
		return true;
	}
	
	
	/**
	 * Returns whether a tile can join patterns with the tiles around it.
	 * @param board The board instance to check this on
	 * @param tile The tile to be checked
	 * @param x The x coordinate of the tile
	 * @param y The y coordinate of the tile
	 */
	//@ requires board != null && tile != null;
	public static boolean canConnectPatterns(Board board, Tile tile, int x, int y) {
		Tile tileUp = board.getTile(x, y - 1).orElse(null);
		Tile tileDown = board.getTile(x, y + 1).orElse(null);
		Tile tileLeft = board.getTile(x - 1, y).orElse(null);
		Tile tileRight = board.getTile(x + 1, y).orElse(null);
		if (tileUp != null && !canConnectVertPattern(tile, tileUp)) {
			return false;
		}
		if (tileDown != null && !canConnectVertPattern(tile, tileDown)) {
			return false;
		}
		if (tileLeft != null && !canConnectHorzPattern(tile, tileLeft)) {
			return false;
		}
		if (tileRight != null && !canConnectHorzPattern(tile, tileRight)) {
			return false;
		}
		if (tileUp != null && tileDown != null && !canConnectVertPattern(tileUp, tileDown)) {
			return false;
		}
		if (tileLeft != null && tileRight != null && !canConnectHorzPattern(tileLeft, tileRight)) {
			return false;
		}
		return true;
	}
	
	/**
	 * Checks if the patterns of 2 tiles can connect vertically.
	 * @param tile1 The first tile
	 * @param tile2 The second tile
	 */
	//@ pure
	private static boolean canConnectVertPattern(Tile tile1, Tile tile2) {
		Pattern p1 = tile1.getVertPattern().orElse(null);
		Pattern p2 = tile2.getVertPattern().orElse(null);
		if (p1 == null) {
			if (p2 == null) {
				return !tile1.equals(tile2) && (tile1.getColor() == tile2.getColor() || 
												tile1.getShape() == tile2.getShape());
			} else {
				return p2.canAdd(tile1);
			}
		} else {
			if (p2 == null) {
				return p1.canAdd(tile2);
			} else if (tile1.getMoveId() != tile2.getMoveId()) {
				return p1.canMerge(p2);
			}
		}
		return true;
	}
	
	/**
	 * Checks if the patterns of 2 tiles can connect horizontally.
	 * @param tile1 The first tile
	 * @param tile2 The second tile
	 */
	//@ pure
	private static boolean canConnectHorzPattern(Tile tile1, Tile tile2) {
		Pattern p1 = tile1.getHorzPattern().orElse(null);
		Pattern p2 = tile2.getHorzPattern().orElse(null);
		if (p1 == null) {
			if (p2 == null) {
				return !tile1.equals(tile2) && (tile1.getColor() == tile2.getColor() || 
												tile1.getShape() == tile2.getShape());
			} else {
				return p2.canAdd(tile1);
			}
		} else {
			if (p2 == null) {
				return p1.canAdd(tile2);
			} else if (tile1.getMoveId() != tile2.getMoveId()) {
				return p1.canMerge(p2);
			}
		}
		return true;
	}
	
	public static boolean canMakeMoveWithTiles(Board b, List<Tile> tiles) {
		if (b.isEmpty()) {
			return true;
		}
		
		List<Tile> boardTiles = b.flattenBoard();
		for (Tile boardTile : boardTiles) {
			int x = boardTile.getX();
			int y = boardTile.getY();
			for (Tile tile : tiles) {
				if (canPlaceTile(b, tile, x - 1, y) ||
								canPlaceTile(b, tile, x + 1, y) ||
								canPlaceTile(b, tile, x, y - 1) ||
								canPlaceTile(b, tile, x, y + 1)) {
					return true;
				}
			}
		}
		return false;
	}
	
}
