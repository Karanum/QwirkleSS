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
	
	//@ private invariant players != null;
	//@ private invariant ui != null;
	//@ private invariant board != null;
	//@ private invariant bag != null;
	private List<Player> players;
	private Player currentPlayer;
	private HumanPlayer localPlayer;
	private UI ui;
	private Board board;
	private Bag bag;
	
	/**
	 * Creates a new Game object.
	 */
	public Game() {
		players = new ArrayList<Player>();
		//ui = new TUI(this);
		board = new Board();
		bag = new Bag();
	}
	
	public void setUI(UI ui) {
		this.ui = ui;
	}
	
	/**
	 * Prepares the game for starting.
	 */
	public void setup() {
		localPlayer = new HumanPlayer(this, "");
		players.add(localPlayer);
	}
	
	/**
	 * Starts the game with the current players.
	 */
	public void start() {
		for (Player p : players) {
			if (!(p instanceof SocketPlayer)) {
				giveTiles(p);
			}
		}
		ui.update();
		currentPlayer = localPlayer;
		localPlayer.determineMove();
		ui.run();
	}
	
	/**
	 * Clears up unused resources at the end of a game.
	 */
	public void dispose() {
		//TODO: Create function body
	}
	
	/**
	 * Determines whether the game has ended and who the winner is.
	 */
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
	public void tradeTiles(Player p, List<Tile> tiles) {
		giveTiles(p);
		bag.returnTiles(tiles);
	}
	
	public Board getBoard() {
		return board;
	}
	
	public HumanPlayer getLocalPlayer() {
		return localPlayer;
	}
	
	public void doMove(Player p, Move move) throws InvalidMoveException, MoveOrderException {
		if (p != currentPlayer) {
			throw new MoveOrderException();
		}
		board.doMove(move);
		giveTiles(p);
		ui.update();
		localPlayer.determineMove();
	}
	
}
