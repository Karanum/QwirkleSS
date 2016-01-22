package ss.qwirkle.common.player.ai;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

import ss.qwirkle.common.Board;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;

public class BasicBehaviour implements Behaviour {

	@Override
	public Move determineMove(Board b, List<Tile> hand) {
		List<Tile> myTiles = new ArrayList<Tile>(hand);
		Random r = new Random();
		Move move = new Move();
		Collections.shuffle(myTiles, r);
		List<Tile> possibleTiles = b.flattenBoard();
		Collections.shuffle(possibleTiles, r);
		boolean result = false;
		while (!result) {
			for (Tile boardTile : possibleTiles) {
				int x = boardTile.getX();
				int y = boardTile.getY();
				for (Tile tile : myTiles) {
					if (!result && !b.hasTile(x + 1, y)) {
						try {
							move.addTile(b, tile, x + 1, y);
							result = true;
						} catch (InvalidMoveException e) { }
					}
					if (!result && !b.hasTile(x - 1, y)) {
						try {
							move.addTile(b, tile, x - 1, y);
							result = true;
						} catch (InvalidMoveException e) { }
					}	
					if (!result && b.hasTile(x, y - 1)) {
						try {
							move.addTile(b, tile, x, y - 1);
							result = true;
						} catch (InvalidMoveException e) { }
					}
					if (!result && !b.hasTile(x, y + 1)) {
						try {
							move.addTile(b, tile, x, y + 1);
							result = true;
						} catch (InvalidMoveException e) { }
					} else { 
						myTiles.remove(tile);
					}
				}	
			}
		}
		return move;
	}
}