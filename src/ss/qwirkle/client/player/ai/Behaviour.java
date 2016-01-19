package ss.qwirkle.client.player.ai;

import java.util.List;

import ss.qwirkle.client.Board;
import ss.qwirkle.client.Move;
import ss.qwirkle.client.tiles.Tile;

/**
 * Interface for AI behavioural patterns used to determine moves for an AIPlayer.
 * @author Karanum
 * @see ss.qwirkle.client.player.AIPlayer AIPlayer
 */
public interface Behaviour {
	
	/**
	 * Asks the behaviour to determine a move.
	 */
	public Move determineMove(Board b, List<Tile> hand);
}
