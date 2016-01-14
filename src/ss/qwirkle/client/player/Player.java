package ss.qwirkle.client.player;

import java.util.List;

import ss.qwirkle.exceptions.NegativeArgumentException;

/**
 * Abstract class representing a player in a Qwirkle match.
 * @author Karanum
 */
public abstract class Player {
	
	//TODO: Remove dummy classes when possible!
	public class Tile {}
	public class Move {}
	
	//@ protected invariant name != null;
	//@ protected invariant score >= 0;
	//@ protected invariant hand != null && hand.size() <= 6;
	protected String name;
	protected int score;
	protected List<Tile> hand;
	
	/**
	 * Asks the player to make a move and send it to the Board for validation.
	 */
	abstract void determineMove();
	
	/**
	 * Creates a new player with the specified name.
	 * @param name The name of the new player
	 */
	//@ requires name != null;
	//@ ensures getName().equals(name);
	//@ ensures getScore() == 0;
	public Player(String name) {
		this.name = name;
		score = 0;
	}
	
	/**
	 * Returns the name of the player.
	 */
	//@ pure
	public String getName() {
		return name;
	}
	
	/**
	 * Returns the score of the player.
	 */
	//@ pure
	public int getScore() {
		return score;
	}
	
	/**
	 * Increments the score of the player.
	 * @param points The amount to increment the score by
	 * @throws NegativeArgumentException If the points parameter is negative
	 */
	//@ ensures points >= 0 ==> getScore() == \old(getScore()) + points;
	public void addScore(int points) throws NegativeArgumentException {
		if (points < 0) {
			throw new NegativeArgumentException();
		}
		score += points;
	}
}
