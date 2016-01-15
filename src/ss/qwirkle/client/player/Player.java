package ss.qwirkle.client.player;

import java.util.List;

import ss.qwirkle.client.Move;
import ss.qwirkle.client.tiles.Tile;
import ss.qwirkle.exceptions.NegativeArgumentException;

/**
 * Abstract class representing a player in a Qwirkle match.
 * @author Karanum
 */
public abstract class Player {
	
	//@ private invariant name != null;
	//@ private invariant score >= 0;
	//@ protected invariant hand != null && hand.size() <= MAX_HAND_SIZE;
	//@ protected invariant moveLog != null;
	private String name;
	private int score;
	protected List<Tile> hand;
	protected List<Move> moveLog;
	
	public static final int MAX_HAND_SIZE = 6;
	
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
	
	/**
	 * Returns the amount of tiles currently in the player's hand.
	 */
	//@ pure
	public int getHandSize() {
		return hand.size();
	}
	
	/**
	 * Adds a number of tiles to the player's hand. Fails if the player would have too many
	 * tiles in their hand after this operation.
	 * @param tiles Tiles to add to the player's hand.
	 */
	//@ requires tiles != null;
	/*@ ensures \old(getHandSize()) + tiles.size() <= MAX_HAND_SIZE ==>
	 					\old(getHandSize()) + tiles.size() == getHandSize(); */
	public void addTilesToHand(List<Tile> tiles) {
		if (getHandSize() + tiles.size() <= MAX_HAND_SIZE) {
			hand.addAll(tiles);
		}
	}
}
