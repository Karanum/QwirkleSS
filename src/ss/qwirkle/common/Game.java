package ss.qwirkle.common;

import java.util.ArrayList;
import java.util.List;

import ss.qwirkle.common.player.HumanPlayer;
import ss.qwirkle.common.player.Player;
import ss.qwirkle.common.player.SocketPlayer;
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
	
	public enum GameType { NONE, SINGLEPLAYER, CLIENT, SERVER };
	public static GameType type = GameType.NONE;
	
	//@ private invariant players != null && !players.isEmpty();
	//@ private invariant Game.type != SERVER ==> localPlayer != null;
	//@ private invariant ui != null;
	//@ private invariant board != null;
	//@ private invariant bag != null;
	private List<Player> players;
	private int currentPlayer;
	private HumanPlayer localPlayer;
	private UI ui;
	private Board board;
	private Bag bag;
	
	/**
	 * Creates a new Game object.
	 */
	public Game() {
		players = new ArrayList<Player>();
		board = new Board();
		bag = new Bag();
		currentPlayer = 0;
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
		for (Player p : players) {
			giveTiles(p);
		}
		ui.update();
		currentPlayer = 0;
		players.get(0).determineMove();
		ui.run();
	}
	
	/**
	 * Clears up unused resources at the end of a game.
	 */
	//@ ensures getBoard().isEmpty();
	public void dispose() {
		players.clear();
		board = new Board();
		bag = new Bag();
	}
	
	/**
	 * Determines whether the game has ended and who the winner is.
	 */
	//@ pure
	public void determineWinner() {
		//TODO: Create function body
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
	}
	
	/**
	 * Returns the main Board object of this game.
	 */
	//@ pure
	public Board getBoard() {
		return board;
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
		giveTiles(p);
	}
	
	/**
	 * Tells the game to advance to the next player's turn.
	 * @param p The player trying to end their turn
	 * @throws MoveOrderException Throws this when the player tries to act out of turn
	 */
	public void nextTurn(Player p) throws MoveOrderException {
		if (p != players.get(currentPlayer)) {
			throw new MoveOrderException();
		}
		ui.update();
		++currentPlayer;
		if (currentPlayer >= players.size()) {
			currentPlayer = 0;
		}
		players.get(currentPlayer).determineMove();
	}
	
}
