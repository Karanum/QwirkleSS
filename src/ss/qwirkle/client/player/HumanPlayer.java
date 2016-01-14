package ss.qwirkle.client.player;

/**
 * A Player that is controlled by the local user.
 * @author Karanum
 */
public class HumanPlayer extends Player {

	/**
	 * Creates a new human player with the specified name.
	 * @param name The name of the new player
	 */
	//@ requires name != null;
	public HumanPlayer(String name) {
		super(name);
	}
	
	/**
	 * Asks the player to determine their next move using user input.
	 */
	@Override
	public void determineMove() {
		
	}
	
}
