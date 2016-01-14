package ss.qwirkle.client.player.ai;

/**
 * Interface for AI behavioural patterns used to determine moves for an AIPlayer.
 * @author Karanum
 * @see ss.qwirkle.client.player.AIPlayer AIPlayer
 */
public interface Behaviour {
	
	/**
	 * Asks the behaviour to determine a move.
	 */
	public void determineMove();
}
