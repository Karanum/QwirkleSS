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

	private Board board;
	private List<Tile> myHand;
	private List<Tile> handCopy;
	private boolean result;
	private Move move;
	
	/**
	 * Asks the behaviour to determine a move.
	 */
	@Override
	public Move determineMove(Board b, List<Tile> hand) {
		move = getPossibleMove(b, hand);
		for (Tile tile : move.getTiles()) {
			hand.remove(tile);
		}
		return move;
	}
	
	public Move getPossibleMove(Board b, List<Tile> hand) {
		board = b;
		move = new Move();
		myHand = hand;
		
		Random r = new Random();
		List<Tile> possibleTiles = b.flattenBoard();
		Collections.shuffle(possibleTiles, r);
		
		result = false;
		if (b.isEmpty()) {
			handCopy = new ArrayList<Tile>(hand);
			Collections.shuffle(handCopy, r);
			try {
				move.addTile(b, handCopy.get(0), 0, 0);
				//hand.remove(myHand.get(0));
			} catch (InvalidMoveException e) { }
			result = true;
		}
		
		while (!result) {
			for (int i = 0; i < possibleTiles.size(); ++i) {
				Tile boardTile = possibleTiles.get(i);
				int x = boardTile.getX();
				int y = boardTile.getY();
				handCopy = new ArrayList<Tile>(hand);
				Collections.shuffle(handCopy, r);
				for (int j = handCopy.size() - 1; j >= 0 && !result; --j) {
					Tile tile = handCopy.get(j);
					
					checkTile(x + 1, y, tile);
					checkTile(x - 1, y, tile);
					checkTile(x, y + 1, tile);
					checkTile(x, y - 1, tile);
				}	
			}
			result = true;
		}
		return move;
	}
	
	private void checkTile(int x, int y, Tile tileInHand) {
		if (result) {
			return;
		}
		if (!board.hasTile(x, y)) {
			try {
				move.addTile(board, tileInHand, x, y);
				//hand.remove(tileInHand);
				result = true;
			} catch (InvalidMoveException e) { }
		}
	}
}