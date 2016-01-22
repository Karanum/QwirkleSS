package ss.qwirkle.common.player;

import java.util.Collections;
import java.util.List;
import java.util.Optional;

import ss.qwirkle.common.Game;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;
import ss.qwirkle.exceptions.MoveOrderException;

/**
 * A Player that is controlled by the local user.
 * @author Karanum
 */
public class HumanPlayer extends Player {

	private Move move;
	private Game game;
	
	/**
	 * Creates a new human player with the specified name.
	 * @param name The name of the new player
	 */
	//@ requires name != null;
	public HumanPlayer(Game game, String name) {
		super(name);
		this.game = game;
	}
	
	/**
	 * Asks the player to determine their next move using user input.
	 */
	@Override
	public void determineMove() {
		move = new Move();
	}
	
	/**
	 * Tells the player to add a tile to their move.
	 * @param handIndex The index of the tile in the player's hand
	 * @param x The x coordinate to place the tile at
	 * @param y The y coordinate to place the tile at
	 * @return Success value
	 */
	//@ requires 0 <= handIndex && handIndex < Player.MAX_HAND_SIZE;
	//@ ensures getCurrentMove().orElse(null) == null ==> !\result;
	public boolean makeMove(int handIndex, int x, int y) throws InvalidMoveException {
		if (move == null || handIndex >= hand.size()) {
			return false;
		}
		Tile tile = hand.get(handIndex);
		move.addTile(game.getBoard(), tile, x, y);
		hand.remove(handIndex);
		return true;
	}
	
	/**
	 * Finishes the player's move, sending it to the game for checking.
	 */
	//@ requires getCurrentMove().orElse(null) != null;
	//@ ensures getCurrentMove().orElse(null) == null;
	public void finishMove() throws InvalidMoveException {
		Move m = move;
		move = null;
		try {
			game.doMove(this, m);
		} catch (MoveOrderException e) {
			System.out.println("ERROR: Player moved out of turn! Name: " + getName());
		} catch (InvalidMoveException e) {
			move = m;
			throw e;
		}
	}
	
	public void resetMove() {
		if (move != null) {
			hand.addAll(move.getTiles());
			Collections.sort(hand);
			move = new Move();
		}
	}
	
	//@ pure
	public Optional<Move> getCurrentMove() {
		return move != null ? Optional.<Move>of(move) : Optional.<Move>empty();
	}
	
	/**
	 * Adds a number of tiles to the player's hand. Fails if the player would have too many
	 * tiles in their hand after this operation. Sorts the hand afterwards.
	 * @param tiles Tiles to add to the player's hand.
	 */
	@Override
	public void addTilesToHand(List<Tile> tiles) {
		super.addTilesToHand(tiles);
		Collections.sort(hand);
	}
	
}
