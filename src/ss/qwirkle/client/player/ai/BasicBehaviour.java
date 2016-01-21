package ss.qwirkle.client.player.ai;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

import ss.qwirkle.client.Board;
import ss.qwirkle.client.Move;
import ss.qwirkle.client.tiles.Tile;

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
						if (b.canPlaceTile(tile, x + 1, y)) {
							result = true;
							move.addTile(tile, x + 1, y);
						}
					}
					if (!result && !b.hasTile(x - 1, y)) {
						if (b.canPlaceTile(tile, x - 1, y)) {
							result = true;
							move.addTile(tile, x - 1, y);
						}
					}	
					if (!result && b.hasTile(x, y - 1)) {
						if (b.canPlaceTile(tile, x, y - 1)) {
							result = true;	
							move.addTile(tile, x, y - 1);
						}
					}
					if (!result && !b.hasTile(x, y + 1)) {
						if (b.canPlaceTile(tile, x, y + 1)) {
							result = true;
							move.addTile(tile, x, y + 1);
						}
					} else { 
						myTiles.remove(tile);
					}
				}	
			}
		}
		return move;
	}
}