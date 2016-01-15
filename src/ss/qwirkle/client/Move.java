package ss.qwirkle.client;

/**
 * The move done by a player.
 * @author Dylan
 */
public class Move {
	//@ private invariant points >= 0;
	private int points;

	/**
	 * returns the rewarded points when doing this move.
	 */
	public int getPoints() {
		return points;
	}
	

}
