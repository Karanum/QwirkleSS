package ss.qwirkle.common.player.ai;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

import ss.qwirkle.common.Board;
import ss.qwirkle.common.BoardChecker;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;

/**
 * Basic AI behaviour, makes random moves.
 * @author Dylan
 */
public class BasicBehaviour implements Behaviour {

	/**
	 * Asks the behaviour to determine a move.
	 */
	@Override
	public Move determineMove(Board b, List<Tile> hand) {
		List<Tile> possibleTiles = b.flattenBoard();
		Random r = new Random();
		Move move = new Move();
		Collections.shuffle(possibleTiles, r);
		
		boolean result = false;
		if (b.isEmpty()) {
			List<Tile> myTiles = new ArrayList<Tile>(hand);
			Collections.shuffle(myTiles, r);
			try {
				move.addTile(b, myTiles.get(0), 0, 0);
				hand.remove(myTiles.get(0));
			} catch (InvalidMoveException e) { }
			result = true;
		}
		
		while (!result) {
			//for (Tile boardTile : possibleTiles) {
			for (int i = 0; i < possibleTiles.size(); ++i) {
				Tile boardTile = possibleTiles.get(i);
				int x = boardTile.getX();
				int y = boardTile.getY();
				List<Tile> myTiles = new ArrayList<Tile>(hand);
				Collections.shuffle(myTiles, r);
				for (int j = myTiles.size() - 1; j >= 0 && !result; --j) {
					Tile tile = myTiles.get(j);
					
					if (!b.hasTile(x + 1, y)) {
						try {
							move.addTile(b, tile, x + 1, y);
							hand.remove(myTiles.get(j));
							result = true;
						} catch (InvalidMoveException e) { }
					} else if (!b.hasTile(x - 1, y)) {
						try {
							move.addTile(b, tile, x - 1, y);
							hand.remove(myTiles.get(j));
							result = true;
						} catch (InvalidMoveException e) { }
					} else if (!b.hasTile(x, y - 1)) {
						try {
							move.addTile(b, tile, x, y - 1);
							hand.remove(myTiles.get(j));
							result = true;
						} catch (InvalidMoveException e) { }
					} else if (!b.hasTile(x, y + 1)) {
						try {
							move.addTile(b, tile, x, y + 1);
							hand.remove(myTiles.get(j));
							result = true;
						} catch (InvalidMoveException e) { }
					}
				}	
			}
			result = true;
		}
		return move;
	}
}