package ss.qwirkle.util;

import java.util.Comparator;

import ss.qwirkle.common.player.Player;

/**
 * Comparator for player scores. Used for ordering players by score.
 * @author Karanum
 */
public class PlayerScoreComparator implements Comparator<Player> {

	/**
	 * Compares players by score. Returns the sign (-1, 0 or 1) of the result.
	 */
	@Override
	public int compare(Player p1, Player p2) {
		return Integer.signum(p1.getScore() - p2.getScore());
	}
	
}
