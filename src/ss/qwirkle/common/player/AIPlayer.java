package ss.qwirkle.common.player;

import java.util.ArrayList;
import java.util.List;

import ss.qwirkle.common.Game;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.player.ai.Behaviour;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;
import ss.qwirkle.exceptions.MoveOrderException;

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
	public AIPlayer(Game game, String name, Behaviour ai) {
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
		if (move.getTiles().size() > 0) {
			try {
				game.doMove(this, move);
			} catch (InvalidMoveException e) {
				e.printStackTrace();
			} catch (MoveOrderException e) {
				e.printStackTrace();
			}
		} else {
			System.out.println("Trading!");
			List<Tile> tiles = new ArrayList<Tile>(hand);
			hand.clear();
			try {
				game.tradeTiles(this, tiles);
			} catch (MoveOrderException e) {
				e.printStackTrace();
			}
		}
	}
	
}
