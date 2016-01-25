package ss.qwirkle.common.player;

import ss.qwirkle.common.Game;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.player.ai.Behaviour;

/**
 * A Player that makes use of a set Behaviour to determine its moves.
 * @author Karanum
 */
public class AIPlayer extends Player {

	//@ private invariant behaviour != null;
	private Behaviour behaviour;
	private Game game;
	
	/**
	 * Creates a new AI player with the given name and behaviour.
	 * @param name The name of the new player
	 * @param ai The behaviour pattern of the player
	 */
	//@ requires name != null;
	//@ requires ai != null;
	//@ requires game != null;
	public AIPlayer(String name, Behaviour ai, Game game) {
		super(name);
		behaviour = ai;
		this.game = game;
	}
	
	/**
	 * Asks the player to determine their next move using their behaviour.
	 */
	@Override
	public void determineMove() {
		Move move = behaviour.determineMove(game.getBoard(), getHand());
		//TODO: Create function body
	}
	
}
