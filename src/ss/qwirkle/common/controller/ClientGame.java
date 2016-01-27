package ss.qwirkle.common.controller;

import java.util.ArrayList;
import java.util.List;

import nl.utwente.ewi.qwirkle.net.IProtocol;
import nl.utwente.ewi.qwirkle.net.IProtocol.Feature;
import ss.qwirkle.QwirkleClient;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.player.HumanPlayer;
import ss.qwirkle.common.player.Player;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.common.ui.UI;
import ss.qwirkle.exceptions.InvalidMoveException;
import ss.qwirkle.exceptions.MoveOrderException;
import ss.qwirkle.network.Client;

public class ClientGame extends Game {

	private Player localPlayer;
	private Client client;
	
	private boolean response;
	private boolean nameAccepted;
	private int playerPref;
	
	public ClientGame() {
		super();
		response = false;
		nameAccepted = false;
		playerPref = 0;
	}
	
	/**
	 * Starts a new client game.
	 */
	@Override
	public void start() {
		if (client == null) {
			return;
		}
		while (localPlayer == null) {
			String name = queryName();
			response = false;
			client.identifyPlayer(name, new ArrayList<Feature>());
			while (!response) {
				while (!client.hasNext()) {
					try {
						Thread.sleep(100);
					} catch (InterruptedException e) { }
				}
				
				client.parseCommand(client.next());
				if (nameAccepted) {
					localPlayer = new HumanPlayer(this, name);
					addPlayer(localPlayer);
				} else {
					System.out.println("That name has already been taken!");
				}
			}
		}
		
		List<Integer> queueList = new ArrayList<Integer>();
		if (playerPref == 1) {
			queueList.add(2);
			queueList.add(3);
			queueList.add(4);
		} else {
			queueList.add(playerPref);
		}
		client.queuePlayer(queueList);
		
		running = true;
		while (running) {
			while (client.hasNext()) {
				client.parseCommand(client.next());
			}
		}
	}
	
	/**
	 * Tells the game that the player's name was denied.
	 */
	public void setNameDenied() {
		response = true;
		nameAccepted = false;
	}
	
	/**
	 * Tells the game that the player's name was accepted.
	 */
	public void setNameAccepted() {
		response = true;
		nameAccepted = true;
	}
	
	/**
	 * Asks the user to input their player name.
	 */
	public String queryName() {
		String name = null;
		while (name == null) {
			name = QwirkleClient.queryName(false);
			if (!name.matches(IProtocol.NAME_REGEX)) {
				name = null;
				getUI().showMessage("Please enter a name between 2 and 16 characters "
									+ "consisting only of letters, digits and underscores");
			}
		}
		return name;
	}
	
	/**
	 * Prepares the game for starting.
	 * @param newUi The UI to use for this game
	 * @param c The Client object that is connected to the server
	 * @param playerNum The preferred amount of players to play with
	 */
	//@ requires newUi != null && c != null;
	public void setup(UI newUi, Client c, int playerNum) {
		super.setup(newUi);
		client = c;
		playerPref = playerNum;
	}
	
	/**
	 * Special stop for when an error occurs before an actual game starts.
	 */
	public void preGameStop() {
		running = false;
		dispose();
		
	}
	
	/**
	 * Clears up resources at the end of the game and stops the client.
	 */
	@Override
	public void dispose() {
		super.dispose();
		if (client.isRunning()) {
			client.quitPlayer();
			client.shutdown();
		}
		client = null;
	}

	/**
	 * Returns GameEndCause.NONE, as the client does not decide if a game ends.
	 */
	@Override
	public GameEndCause testGameOver() {
		return GameEndCause.NONE;
	}
	
	/**
	 * Returns the local player.
	 */
	//@ pure
	public Player getLocalPlayer() {
		return localPlayer;
	}

	@Override
	public void tradeTiles(Player p, List<Tile> tiles) throws MoveOrderException {
		if (getCurrentPlayer() != p) {
			throw new MoveOrderException();
		}
		client.tradeMove(tiles);
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
		if (getCurrentPlayer() != p) {
			throw new MoveOrderException();
		}
		client.sendMove(move);
	}
	
}
