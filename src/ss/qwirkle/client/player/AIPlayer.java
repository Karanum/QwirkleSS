package ss.qwirkle.client.player;

import ss.qwirkle.client.player.ai.Behaviour;

/**
 * A Player that makes use of a set Behaviour to determine its moves.
 * @author Karanum
 */
public class AIPlayer extends Player {

	//@ private invariant behaviour != null;
	private Behaviour behaviour;
	
	/**
	 * Creates a new AI player with the given name and behaviour.
	 * @param name The name of the new player
	 * @param ai The behaviour pattern of the player
	 */
	//@ requires name != null;
	//@ requires ai != null;
	public AIPlayer(String name, Behaviour ai) {
		super(name);
		behaviour = ai;
	}
	
	/**
	 * Asks the player to determine their next move using their behaviour.
	 */
	@Override
	public void determineMove() {
		behaviour.determineMove();
	}
	
}
