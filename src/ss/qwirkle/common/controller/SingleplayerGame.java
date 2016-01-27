package ss.qwirkle.common.controller;

import java.util.List;

import ss.qwirkle.common.Bag;
import ss.qwirkle.common.BoardChecker;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.player.HumanPlayer;
import ss.qwirkle.common.player.Player;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;
import ss.qwirkle.exceptions.MoveOrderException;

/**
 * Singleplayer implementation of the Game class.
 * @author Karanum
 */
public class SingleplayerGame extends Game {
	
	//@ private invariant bag != null;
	private HumanPlayer localPlayer;
	private Bag bag;
	
	/**
	 * Creates a new Game object.
	 */
	public SingleplayerGame() {
		super();
		bag = new Bag();
	}
	
	/**
	 * Adds a player to the list of players.
	 * If a HumanPlayer is added, it will become the new local player.
	 * @param p The player to add
	 */
	//@ requires p != null;
	@Override
	public void addPlayer(Player p) {
		if (p instanceof HumanPlayer) {
			localPlayer = (HumanPlayer) p;
		}
		super.addPlayer(p);
	}
	
	/**
	 * Starts a singleplayer game.
	 */
	@Override
	public void start() {
		running = true;
		for (Player p : getPlayers()) {
			giveTiles(p);
		}
		currentPlayer = 0;
		(new Thread(getUI())).start();
		
		while (running) {
			Player player = getPlayers().get(currentPlayer);
			if (localPlayer == null || player instanceof HumanPlayer) {
				getUI().update();
			}
			player.determineMove();
			
			GameEndCause cause = testGameOver();
			if (cause != GameEndCause.NONE) {
				stop(cause);
			} else if (!getPlayers().isEmpty()) {
				do {
					try {
						currentPlayer = (currentPlayer + 1) % getPlayers().size();
					} catch (ArithmeticException e) {
						break;
					}
				} while (bag.getSize() == 0 && !BoardChecker.canMakeMoveWithTiles(getBoard(), 
												getPlayers().get(currentPlayer).getHand()));
			}
		}
	}
	
	/**
	 * Clears up unused resources at the end of a game.
	 */
	//@ ensures getLocalPlayer() == null;
	@Override
	public void dispose() {
		super.dispose();
		if (localPlayer != null) {
			localPlayer.abortMove();
			localPlayer = null;
		}
		bag = new Bag();
	}
	
	/**
	 * Checks if the game should end, and if so, formally ends the game.
	 */
	@Override
	public GameEndCause testGameOver() {
		if (!running) {
			return GameEndCause.ERROR;
		}
		
		Player player = getPlayers().get(currentPlayer);
		if (player.getHand().isEmpty() && bag.getSize() == 0) {
			player.addScore(Player.MAX_HAND_SIZE);
			return GameEndCause.EMPTY_HAND;
		}
		
		List<Tile> allGameTiles = bag.getAllTiles();
		for (Player p : getPlayers()) {
			allGameTiles.addAll(p.getHand());
		}
		if (!BoardChecker.canMakeMoveWithTiles(getBoard(), allGameTiles)) {
			return GameEndCause.NO_MOVES;
		}
		
		return GameEndCause.NONE;
	}
	
	/**
	 * Gives tiles to the specified player to fill up their hand.
	 * @param p The player to give tiles to
	 */
	//@ requires p != null;
	//@ ensures p.getHandSize() == Player.MAX_HAND_SIZE;
	public void giveTiles(Player p) {
		int amount = Player.MAX_HAND_SIZE - p.getHandSize();
		if (amount > 0) {
			List<Tile> tiles = bag.getTiles(amount);
			p.addTilesToHand(tiles);
		}
	}
	
	/**
	 * Gives tiles to the specified player in exchange for some of their tiles.
	 * @param p The player to give tiles to
	 * @param tiles The tiles the player wants to exchange
	 */
	//@ requires p != null;
	//@ requires tiles != null;
	//@ requires tiles.size() == Player.MAX_HAND_SIZE - p.getHandSize();
	//@ ensures p.getHandSize() == Player.MAX_HAND_SIZE;
	public void tradeTiles(Player p, List<Tile> tiles) throws MoveOrderException {
		if (p != getCurrentPlayer()) {
			throw new MoveOrderException();
		}
		giveTiles(p);
		bag.returnTiles(tiles);
		if (p.getHand().size() < Player.MAX_HAND_SIZE) {
			giveTiles(p);
		}
	}
	
	/**
	 * Returns the Bag object of this game.
	 */
	//@ pure
	public Bag getBag() {
		return bag;
	}
	
	/**
	 * Returns the local player.
	 */
	//@ pure
	public HumanPlayer getLocalPlayer() {
		return localPlayer;
	}
	
	/**
	 * Sets the current player whose turn it is.
	 * @param name The name of the current player
	 */
	//@ requires name != null;
	@Override
	public void setCurrentPlayer(String name) {
		super.setCurrentPlayer(name);
		if (getCurrentPlayer() == localPlayer) {
			localPlayer.determineMove();
		}
	}
	
	/**
	 * Performs a move for a player by sending it to the board
	 * and passing any exceptions back to the player.
	 * @param p The player who makes the move
	 * @param move The move that needs to be performed
	 * @throws InvalidMoveException Throws this when the board considers the move faulty
	 * @throws MoveOrderException Throws this when the player tries to act out of turn
	 */
	//@ requires p != null && move != null;
	@Override
	public void doMove(Player p, Move move) throws InvalidMoveException, MoveOrderException {
		super.doMove(p, move);
		giveTiles(p);
	}
	
}
