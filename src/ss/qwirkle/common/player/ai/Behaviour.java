package ss.qwirkle.common.player.ai;

import java.util.List;

import ss.qwirkle.common.Board;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.tiles.Tile;

/**
 * Interface for AI behavioural patterns used to determine moves for an AIPlayer.
 * @author Karanum
 * @see ss.qwirkle.common.player.AIPlayer AIPlayer
 */
public interface Behaviour {
	
	/**
	 * Asks the behaviour to determine a move.
	 */
	public Move determineMove(Board b, List<Tile> hand);
}
