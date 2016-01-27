package ss.qwirkle.common.player;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

import ss.qwirkle.common.Move;
import ss.qwirkle.common.controller.Game;
import ss.qwirkle.common.controller.SingleplayerGame;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;
import ss.qwirkle.exceptions.MoveOrderException;

/**
 * A Player that is controlled by the local user.
 * @author Karanum
 */
public class HumanPlayer extends Player {

	//@ private invariant game != null;
	private Move move;
	private Game game;
	private boolean awaitingMove;
	
	private List<Tile> tradedTiles;
	
	/**
	 * Creates a new human player with the specified name.
	 * @param name The name of the new player
	 */
	//@ requires name != null;
	//@ requires game != null;
	public HumanPlayer(Game game, String name) {
		super(name);
		this.game = game;
		awaitingMove = false;
	}
	
	public void tradeTiles(List<Tile> tiles) {
		tradedTiles = new ArrayList<Tile>(tiles);
		hand.removeAll(tiles);
		try {
			game.tradeTiles(this, tiles);
			awaitingMove = false;
		} catch (MoveOrderException e) {
			System.out.println("ERROR: Player moved out of turn! Name: " + getName());
			hand.addAll(tradedTiles);
		}
	}
	
	/**
	 * Used by the network client to notify that the player's trade failed.
	 */
	//@ requires message != null;
	@Override
	public void tradeFailed(String message) {
		hand.addAll(tradedTiles);
		game.getUI().showMessage(message);
	}
	
	/**
	 * Asks the player to determine their next move using user input.
	 * In a singleplayer game, this will pause the game until the move finishes.
	 */
	@Override
	public void determineMove() {
		move = new Move();
		awaitingMove = true;
		if (game instanceof SingleplayerGame) {
			while (awaitingMove) {
				try {
					Thread.sleep(100);
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
			}
		}
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
	 * Forcefully aborts the player's turn, in case the game ends for example.
	 */
	public void abortMove() {
		awaitingMove = false;
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
			awaitingMove = false;
		} catch (MoveOrderException e) {
			System.out.println("ERROR: Player moved out of turn! Name: " + getName());
		} catch (InvalidMoveException e) {
			move = m;
			throw e;
		}
	}
	
	/**
	 * Resets the current move, moving all tiles back to the player's hand.
	 */
	/*@ ensures \old(getCurrentMove().orElse(null)) != null ==>
						getCurrentMove().orElse(null).getTiles().isEmpty(); */
	public void resetMove() {
		if (move != null) {
			hand.addAll(move.getTiles());
			Collections.sort(hand);
			move = new Move();
		}
	}
	
	/**
	 * Returns the current move in progress of the player, or null if it's not their turn.
	 */
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
