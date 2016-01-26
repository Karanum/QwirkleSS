package ss.qwirkle.common;

import java.util.ArrayList;
import java.util.List;

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
public class Game {
	
	/**
	 * List of possible game types.
	 * @author Karanum
	 */
	public enum GameType { NONE, SINGLEPLAYER, CLIENT, SERVER };
	
	/**
	 * List of causes for the game to end.
	 * @author Karanum
	 */
	public enum GameEndCause { NONE, EMPTY_HAND, NO_MOVES, ERROR };
	
	public static GameType type = GameType.NONE;
	
	//@ private invariant players != null && !players.isEmpty();
	//@ private invariant ui != null;
	//@ private invariant board != null;
	//@ private invariant bag != null;
	private List<Player> players;
	private HumanPlayer localPlayer;
	private UI ui;
	private Board board;
	private Bag bag;
	
	private int currentPlayer;
	private boolean running;
	
	/**
	 * Creates a new Game object.
	 */
	public Game() {
		players = new ArrayList<Player>();
		board = new Board();
		bag = new Bag();
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
	 * If a HumanPlayer is added, it will become the new local player.
	 * @param p The player to add
	 */
	//@ requires p != null;
	public void addPlayer(Player p) {
		if (p instanceof HumanPlayer) {
			localPlayer = (HumanPlayer) p;
		}
		players.add(p);
	}
	
	/**
	 * Starts the game with the current players.
	 */
	public void start() {
		running = true;
		for (Player p : players) {
			giveTiles(p);
		}
		currentPlayer = 0;
		(new Thread(ui)).start();
		
		while (running) {
			Player player = players.get(currentPlayer);
			if (localPlayer == null || player instanceof HumanPlayer) {
				ui.update();
			}
			player.determineMove();
			
			GameEndCause cause = testGameOver();
			if (cause != GameEndCause.NONE) {
				stop(cause);
			} else {
				do {
					currentPlayer = (currentPlayer + 1) % players.size();
				} while (!BoardChecker.canMakeMoveWithTiles(board, 
										players.get(currentPlayer).getHand()));
			}
		}
	}
	
	/**
	 * Stops the game and tells the UI to show the results.
	 */
	//@ requires cause != null;
	public void stop(GameEndCause cause) {
		if (running) {
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
	//@ ensures getLocalPlayer() == null;
	public void dispose() {
		if (localPlayer != null) {
			localPlayer.abortMove();
			localPlayer = null;
		}
		players.clear();
		board = new Board();
		bag = new Bag();
	}
	
	/**
	 * Checks if the game should end, and if so, formally ends the game.
	 */
	public GameEndCause testGameOver() {
		if (!running) {
			return GameEndCause.ERROR;
		}
		
		Player player = players.get(currentPlayer);
		if (player.getHand().isEmpty() && bag.getSize() == 0) {
			player.addScore(Player.MAX_HAND_SIZE);
			return GameEndCause.EMPTY_HAND;
		}
		
		List<Tile> allGameTiles = bag.getAllTiles();
		for (Player p : players) {
			allGameTiles.addAll(p.getHand());
		}
		if (!BoardChecker.canMakeMoveWithTiles(board, allGameTiles)) {
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
		if (p != players.get(currentPlayer)) {
			throw new MoveOrderException();
		}
		giveTiles(p);
		bag.returnTiles(tiles);
		if (p.getHand().size() < Player.MAX_HAND_SIZE) {
			giveTiles(p);
		}
	}
	
	/**
	 * Returns the main Board object of this game.
	 */
	//@ pure
	public Board getBoard() {
		return board;
	}
	
	/**
	 * Returns the Bag object of this game.
	 */
	//@ pure
	public Bag getBag() {
		return bag;
	}
	
	/**
	 * Returns the list of players.
	 */
	//@ pure
	public List<Player> getPlayers() {
		return players;
	}
	
	/**
	 * Returns the local player.
	 */
	//@ pure
	public HumanPlayer getLocalPlayer() {
		return localPlayer;
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
		giveTiles(p);
	}
	
}
