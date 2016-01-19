package ss.qwirkle.client.player;

import java.util.Collections;
import java.util.List;

import ss.qwirkle.client.Move;
import ss.qwirkle.client.tiles.Tile;

/**
 * A Player that is controlled by the local user.
 * @author Karanum
 */
public class HumanPlayer extends Player {

	private Move move;
	
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
	//@ ensures move == null ==> !\result;
	public boolean makeMove(int handIndex, int x, int y) {
		if (move == null || handIndex >= hand.size()) {
			return false;
		}
		Tile tile = hand.get(handIndex);
		//TODO: Add tile to move
		return true;
	}
	
	/**
	 * Finishes the player's move, sending it to the board for checking.
	 */
	//@ requires move != null;
	//@ ensures move == null;
	public void finishMove() {
		//TODO: Send move to board for checking
		move = null;
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
