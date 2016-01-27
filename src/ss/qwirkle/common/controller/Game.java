package ss.qwirkle.common.controller;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import ss.qwirkle.common.Bag;
import ss.qwirkle.common.Board;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.controller.Game.GameEndCause;
import ss.qwirkle.common.player.HumanPlayer;
import ss.qwirkle.common.player.Player;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.common.ui.UI;
import ss.qwirkle.exceptions.InvalidMoveException;
import ss.qwirkle.exceptions.MoveOrderException;

/**
 * Controller class for the game. Starts matches and handles communication between
 * the UI and the rest of the system.
 * @author Karanum
 */
public abstract class Game {

	/**
	 * List of causes for the game to end.
	 * @author Karanum
	 */
	public enum GameEndCause { NONE, EMPTY_HAND, NO_MOVES, UNSPECIFIED, ERROR };
	
	//@ private invariant players != null;
	//@ private invariant ui != null;
	//@ private invariant board != null;
	private List<Player> players;
	private UI ui;
	private Board board;
	
	protected boolean running;
	protected int currentPlayer;
	
	/**
	 * Creates a new Game object.
	 */
	public Game() {
		players = new ArrayList<Player>();
		board = new Board();
		currentPlayer = 0;
		running = false;
	}
	
	/**
	 * Prepares the game for starting.
	 * @param newUi The UI to use for this game
	 */
	//@ requires newUi != null;
	public void setup(UI newUi) {
		ui = newUi;
	}
	
	/**
	 * Adds a player to the list of players.
	 * @param p The player to add
	 */
	//@ requires p != null;
	public void addPlayer(Player p) {
		players.add(p);
	}
	
	/**
	 * Stops the game and tells the UI to show the results.
	 */
	//@ requires cause != null;
	public void stop(GameEndCause cause) {
		if (running) {
			ui.update();
			ui.gameOver(cause);
			running = false;
			ui.stop();
			dispose();
		}
	}
	
	/**
	 * Clears up unused resources at the end of a game.
	 */
	//@ ensures getBoard().isEmpty();
	//@ ensures getPlayers().size() == 0;
	public void dispose() {
		players.clear();
		board = new Board();
	}
	
	/**
	 * Returns the main Board object of this game.
	 */
	//@ pure
	public Board getBoard() {
		return board;
	}
	
	/**
	 * Returns the list of players.
	 */
	//@ pure
	public List<Player> getPlayers() {
		return players;
	}
	
	/**
	 * Returns the current player.
	 */
	//@ pure
	public Player getCurrentPlayer() {
		return players.get(currentPlayer);
	}
	
	/**
	 * Sets the current player whose turn it is.
	 * @param name The name of the current player
	 */
	//@ requires name != null;
	public void setCurrentPlayer(String name) {
		for (int i = 0; i < players.size(); ++i) {
			if (players.get(i).getName().equals(name)) {
				currentPlayer = i;
			}
		}
	}
	
	/**
	 * Returns a player by their name.
	 * @param name The name of the player
	 */
	//@ requires name != null;
	public Optional<Player> getPlayerByName(String name) {
		for (Player p : players) {
			if (p.getName().equals(name)) {
				return Optional.of(p);
			}
		}
		return Optional.empty();
	}
	
	/**
	 * Returns the UI.
	 */
	//@ pure
	public UI getUI() {
		return ui;
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
	public void doMove(Player p, Move move) throws InvalidMoveException, MoveOrderException {
		if (p != players.get(currentPlayer)) {
			throw new MoveOrderException();
		}
		board.doMove(move);
		p.addScore(move.getPoints());
	}
	
	/**
	 * Starts a game.
	 */
	public abstract void start();
	
	/**
	 * Checks if the game should end, and if so, formally ends the game.
	 */
	public abstract GameEndCause testGameOver();
	
	/**
	 * Returns the local player.
	 */
	//@ pure
	public abstract Player getLocalPlayer();
	
	/**
	 * Gives tiles to the specified player in exchange for some of their tiles.
	 * @param p The player to give tiles to
	 * @param tiles The tiles the player wants to exchange
	 */
	//@ requires p != null;
	//@ requires tiles != null;
	//@ requires tiles.size() == Player.MAX_HAND_SIZE - p.getHandSize();
	//@ ensures p.getHandSize() == Player.MAX_HAND_SIZE;
	public abstract void tradeTiles(Player p, List<Tile> tiles) throws MoveOrderException;
	
}
