package ss.qwirkle.client;

import java.util.ArrayList;
import java.util.List;

import ss.qwirkle.client.player.Player;
import ss.qwirkle.client.tiles.Tile;
import ss.qwirkle.client.ui.TUI;
import ss.qwirkle.client.ui.UI;

/**
 * Controller class for the game. Starts matches and handles communication between
 * the UI and the rest of the system.
 * @author Karanum
 */
public class Game {
	
	//@ private invariant players != null;
	//@ private invariant ui != null;
	//@ private invariant board != null;
	//@ private invariant bag != null;
	private List<Player> players;
	private UI ui;
	private Board board;
	private Bag bag;
	
	/**
	 * Creates a new Game object.
	 */
	public Game() {
		players = new ArrayList<Player>();
		ui = new TUI(this);
		board = new Board();
		bag = new Bag();
	}
	
	/**
	 * Prepares the game for starting.
	 */
	public void setup() {
		//TODO: Create function body
	}
	
	/**
	 * Starts the game with the current players.
	 */
	public void start() {
		//TODO: Create function body
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
	
}
