package ss.qwirkle.client;

/**
 * Object representing a move done by the player.
 * @author Dylan
 */
public class Move {
	
	//@ private invariant points >= 0;
	private int points;
	
	/**
	 * Creates an empty move object.
	 */
	public Move() {
		points = 0;
	}

	/**
	 * Returns the rewarded points for doing this move.
	 */
	public int getPoints() {
		return points;
	}

}
