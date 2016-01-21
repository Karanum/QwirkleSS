package ss.qwirkle.client;

import ss.qwirkle.client.tiles.ColorPattern;
import ss.qwirkle.client.tiles.Pattern;
import ss.qwirkle.client.tiles.Tile;
import ss.qwirkle.util.Range;

public abstract class BoardChecker {

	public static boolean canPlaceTile(Board board, Tile tile, int x, int y) {
		if (board.isEmpty()) {
			if (x == 0 && y == 0) {
				return true;
			}
		}
		if (board.hasTile(x, y)) {
			return false;
		}
		if (!isCoordAttached(board, x, y)) {
			return false;
		}
		return canConnectPatterns(board, tile, x, y);
	}
	
	public static boolean isCoordAttached(Board board, int x, int y) {
		Tile tileUp = board.getTile(x, y - 1).orElse(null);
		Tile tileDown = board.getTile(x, y + 1).orElse(null);
		Tile tileLeft = board.getTile(x - 1, y).orElse(null);
		Tile tileRight = board.getTile(x + 1, y).orElse(null);
		return tileUp != null || tileDown != null || tileLeft != null || tileRight != null;
	}
	
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
		return true;
	}
	
	private static boolean canConnectVertPattern(Tile tile1, Tile tile2) {
		Pattern p1 = tile1.getVertPattern().orElse(null);
		Pattern p2 = tile2.getVertPattern().orElse(null);
		if (p1 == null) {
			if (p2 == null) {
				return !tile1.equals(tile2);
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
	
	private static boolean canConnectHorzPattern(Tile tile1, Tile tile2) {
		Pattern p1 = tile1.getHorzPattern().orElse(null);
		Pattern p2 = tile2.getHorzPattern().orElse(null);
		if (p1 == null) {
			if (p2 == null) {
				return !tile1.equals(tile2);
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
	
}
