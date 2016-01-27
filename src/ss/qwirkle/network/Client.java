package ss.qwirkle.network;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import nl.utwente.ewi.qwirkle.net.IProtocol;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.controller.ClientGame;
import ss.qwirkle.common.controller.Game.GameEndCause;
import ss.qwirkle.common.player.Player;
import ss.qwirkle.common.player.ServerPlayer;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;
import ss.qwirkle.exceptions.MoveOrderException;

/**
 * Client class for communicating with a remote server.
 * @author Dylan
 */
public class Client extends Thread {
	
	//@ private invariant sock != null;
	//@ private invariant in != null;
	//@ private invariant out != null;
	//@ private invariant game != null;
	private Socket sock;
	private BufferedReader in;
	private BufferedWriter out;
	private ClientGame game;
	private List<String> buffer;
	
	private boolean running;
	
	/**
	 * Creates a new Client that tries to connect to a remote host.
	 * @param host Hostname of the server
	 * @param port Port of the server
	 */
	//@ requires game != null && host != null;
	//@ requires port > 0 && port < 25566;
	public Client(ClientGame game, InetAddress host, int port) {
		this.game = game;
		try {
			sock = new Socket(host, port);
	    	in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
	    	out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
        } catch (IOException e) {
            System.out.println("ERROR: could not connect to a server on " + host
                    			+ ", port " + port);
		}
		buffer = Collections.synchronizedList(new ArrayList<String>());
	}
	
	/**
	 * Returns whether the client is connected and running.
	 */
	//@ pure
	public boolean isRunning() {
		return running;
	}
	
	/**
	 * Sends a message to the connected server.
	 * @param message The message to send, should follow the protocol
	 * @see nl.utwente.ewi.qwirkle.net.IProtocol IProtocol
	 */
	//@ requires message != null;
	public void sendMessage(String message) {
		try {
			out.write(message);
			out.newLine();
			out.flush();
			System.out.println("[OUT] " + message);
		} catch (IOException e) {
			System.out.println("Connection has been lost.");
			shutdown();
			game.stop(GameEndCause.ERROR);
		}
    }
	
	/**
	 * Closes the connection with the server.
	 */
	public void shutdown() {
		try {
			sock.close();
			in.close();
			out.close();
		} catch (IOException e) {
			e.printStackTrace();
		}	
		running = false;
	}
	
	/**
	 * Starts polling for messages from the server.
	 */
	@Override
	public void run() {
		running = in != null;
		while (running) {
			try {
				while (in.ready()) {
					String input = in.readLine();
					System.out.println("[IN] " + input);
					buffer.add(input);
				}
			} catch (IOException e) {
				System.out.println("Connection has been lost.");
				shutdown();
				game.stop(GameEndCause.ERROR);
			}
		}
	}
	
	/**
	 * Sends a move to the server.
	 * @param m The move to send
	 */
	//@ requires m != null;
	public void sendMove(Move m) {
		String message = IProtocol.CLIENT_MOVE_PUT;
		for (Tile t : m.getTiles()) {
			message += String.format(" %d@%d,%d", t.toInt(), t.getX(), t.getY());
		}
		sendMessage(message);
	}
	
	/**
	 * Sends a trade to the server.
	 * @param tiles The tiles to trade
	 */
	//@ requires tiles != null && !tiles.isEmpty();
	public void tradeMove(List<Tile> tiles) {
		String message = IProtocol.CLIENT_MOVE_TRADE;
		for (Tile t: tiles) {
			message += " " + t.toInt();
		}
		sendMessage(message);
	}
	
	/**
	 * Asks the server to add this client to the queue.
	 * @param numbers The preferred number of players to play with
	 */
	//@ requires numbers != null && !numbers.isEmpty();
	public void queuePlayer(List<Integer> numbers) {
		String message = IProtocol.CLIENT_QUEUE;
		message += " ";
		Iterator<Integer> iterator = numbers.iterator();
		while (iterator.hasNext()) {
			message += iterator.next();
			if (iterator.hasNext()) {
				message += ",";
			}
		}
		sendMessage(message);
	}
	
	/**
	 * Tells the server to consider this client disconnected.
	 */
	public void quitPlayer() {
		String message = IProtocol.CLIENT_QUIT;
		sendMessage(message);
	}
	
	/**
	 * Identifies the player to the server.
	 * @param name The name of the local player
	 * @param features The features this client supports
	 */
	//@ requires name != null && features != null;
	public void identifyPlayer(String name, List<IProtocol.Feature> features) {
		String message = IProtocol.CLIENT_IDENTIFY;
		message += " " + name;
		if (!features.isEmpty()) {
			message += " ";
			Iterator<IProtocol.Feature> iterator = features.iterator();
			while (iterator.hasNext()) {
				message += iterator.next();
				if (iterator.hasNext()) {
					message += ",";
				}
			}
		}
		sendMessage(message);
	}
	
	/**
	 * Returns whether the client's message buffer contains any messages.
	 */
	//@ pure
	public boolean hasNext() {
		return !buffer.isEmpty();
	}
	
	/**
	 * Returns the oldest message in the message buffer, if one exists.
	 */
	//@ ensures !hasNext() ==> \result == null;
	public String next() {
		if (!hasNext()) {
			return null;
		}
		return buffer.remove(0);
	}
	
	/**
	 * Parses an incoming command from the server.
	 * @param message The incoming message
	 */
	//@ requires message != null;
	public void parseCommand(String message) {
		String[] args = message.split(" ");
		switch (args[0]) {
			case IProtocol.SERVER_DRAWTILE:
				doDrawTile(args);
				break;
			case IProtocol.SERVER_MOVE_PUT:
				doMovePut(args);
				break;
			case IProtocol.SERVER_ERROR:
				handleError(args);
				break;
			case IProtocol.SERVER_GAMEEND:
				endGame(args);
				break;
			case IProtocol.SERVER_GAMESTART:
				doGameStart(args);
				break;
			case IProtocol.SERVER_IDENTIFY:
				confirmIdentify();
				break;
			case IProtocol.SERVER_MOVE_TRADE:
				doMoveTrade(args);
				break;
			case IProtocol.SERVER_TURN:
				doServerTurn(args);
				break;
			case IProtocol.SERVER_PASS:
				showPassMessage(args);
				break;
			case IProtocol.SERVER_QUEUE:
				confirmQueue();
				break;
		}
	}
	
	/**
	 * Command executor for SERVER_GAMEEND.
	 */
	private void endGame(String[] args) {
		if (args.length < 2 + game.getPlayers().size()) {
			game.getUI().showMessage("ERROR: Server has sent an invalid message!");
			return;
		}
		
		GameEndCause cause = GameEndCause.UNSPECIFIED;
		if (args[1].equalsIgnoreCase("ERROR")) {
			cause = GameEndCause.ERROR;
		}
		for (int i = 2; i < args.length; ++i) {
			String[] scoreArgs = args[i].split(",");
			int score = Integer.parseInt(scoreArgs[0]);
			Player p = game.getPlayerByName(args[1]).orElse(null);
			if (p != null) {
				p.setScore(score);
			}
		}
		game.stop(cause);
	}
	
	/**
	 * Command executor for SERVER_PASS.
	 */
	private void showPassMessage(String[] args) {
		if (args.length < 2) {
			game.getUI().showMessage("ERROR: Server has sent an invalid message!");
			return;
		}
		game.getUI().showMessage("Player " + args[1] + " could not make a move and was skipped!");
	}
	
	/**
	 * Command executor for SERVER_QUEUE.
	 */
	private void confirmQueue() {
		game.getUI().showMessage("You have been queued! Waiting for a match...");
	}
	
	/**
	 * Command executor for SERVER_IDENTIFY.
	 * Does not accept arguments because no features are included anyway.
	 */
	private void confirmIdentify() {
		game.setNameAccepted();
	}
	
	/**
	 * Command executor for SERVER_TURN.
	 */
	private void doServerTurn(String[] args) {
		if (args.length < 2) {
			game.getUI().showMessage("ERROR: Server has sent an invalid message!");
			return;
		}
		game.setCurrentPlayer(args[1]);
	}
	
	/**
	 * Command executor for SERVER_GAMESTART.
	 */
	private void doGameStart(String[] args) {
		if (args.length < 3) {
			game.getUI().showMessage("ERROR: Server has sent an invalid message!");
			return;
		}
		
		for (int i = 1; i < args.length; ++i) {
			String name = args[i];
			if (!name.equals(game.getLocalPlayer().getName())) {
				game.addPlayer(new ServerPlayer(args[i]));
			}
		}
		
		game.getUI().showMessage("A match was found! Starting game now...");
		(new Thread(game.getUI())).start();
		game.getUI().update();
	}
	
	/**
	 * Command executor for SERVER_MOVE_PUT.
	 */
	private void doMovePut(String[] args) {
		if (args.length < 2) {
			game.getUI().showMessage("ERROR: Server has sent an invalid message!");
			return;
		}
		
		Move move = new Move();
		Pattern pattern = Pattern.compile("(\\d+)@(-?\\d+),(-?\\d+)");
		for (int i = 1; i < args.length; ++i) {
			String tileString = args[i];
			Matcher match = pattern.matcher(tileString);
			if (match.matches()) {
				int tileId = Integer.parseInt(match.group(1));
				int x = Integer.parseInt(match.group(2));
				int y = Integer.parseInt(match.group(3));
				Tile tile = new Tile(tileId);
				try {
					move.addTile(game.getBoard(), tile, x, y);
				} catch (InvalidMoveException e) {
					game.getUI().showMessage("ERROR: Server permitted a move that's not allowed!");
				}
			}
		}
		
		try {
			game.doRemoteMove(game.getCurrentPlayer(), move);
			game.getUI().update();
		} catch (InvalidMoveException e) {
			game.getUI().showMessage("ERROR: Server permitted a move that's not allowed!");
		} catch (MoveOrderException e) { }
	}
	
	/**
	 * Command executor for SERVER_MOVE_TRADE.
	 */
	private void doMoveTrade(String[] args) {
		if (args.length < 2) {
			game.getUI().showMessage("ERROR: Server has sent an invalid message!");
			return;
		}
		
		Player p = game.getCurrentPlayer();
		if (p != game.getLocalPlayer()) {
			game.getUI().showMessage("Player " + p.getName() + " just traded " 
										+ args[1] + "tiles");
		}
	}
	
	/**
	 * Command executor for SERVER_DRAWTILE.
	 */
	private void doDrawTile(String[] args) {
		if (args.length < 2) {
			game.getUI().showMessage("ERROR: Server has sent an invalid message!");
			return;
		}
		
		List<Tile> tiles = new ArrayList<Tile>();
		for (int i = 1; i < args.length; ++i) {
			System.out.println("Got tile: " + args[i]);
			int tileInt = Integer.parseInt(args[i]);
			tiles.add(new Tile(tileInt));
		}
		game.getLocalPlayer().addTilesToHand(tiles);
		game.getUI().update();
	}
	
	/**
	 * Delegation command for the different errors the server can throw.
	 */
	private void handleError(String[] args) {
		if (args.length < 3) {
			game.getUI().showMessage("ERROR: Server has sent an invalid message!");
			return;
		}
		
		int errorCode;
		try {
			errorCode = Integer.parseInt(args[1]);
		} catch (NumberFormatException e) {
			errorCode = IProtocol.Error.valueOf(args[1]).ordinal();
		}
		String message = args[2];
		
		IProtocol.Error error = null;
		for (IProtocol.Error e : IProtocol.Error.values()) {
			if (e.ordinal() == errorCode) {
				error = e;
				break;
			}
		}
		if (error == null) {
			game.getUI().showMessage("ERROR: Server has sent an unknown error code");
			return;
		}
		
		switch (error) {
			case DECK_EMPTY:
				game.getLocalPlayer().tradeFailed(message);
				break;
			case CHALLENGE_SELF:
				game.getUI().showMessage("ERROR: Server has sent an invalid message!");
				break;
			case ILLEGAL_STATE:
				game.getUI().showMessage("ERROR: Something just happened out of turn!");
				break;
			case INVALID_CHANNEL:
				game.getUI().showMessage("ERROR: Server has sent an invalid message!");
				break;
			case INVALID_COMMAND:
				game.getUI().showMessage("ERROR: Client has sent an invalid command!");
				break;
			case INVALID_PARAMETER:
				game.getUI().showMessage("ERROR: Client has sent an invalid command!");
				break;
			case MOVE_INVALID:
				game.getLocalPlayer().moveFailed(message);
				break;
			case MOVE_TILES_UNOWNED:
				game.getUI().showMessage("ERROR: Player hand is out of sync with server!");
				break;
			case NAME_INVALID:
				game.setNameDenied();
				break;
			case NAME_USED:
				game.setNameDenied();
				break;
			case NOT_CHALLENGED:
				game.getUI().showMessage("ERROR: Server has sent an invalid message!");
				break;
			case QUEUE_INVALID:
				game.getUI().showMessage(message);
				game.preGameStop();
				break;
			case TRADE_FIRST_TURN:
				game.getLocalPlayer().tradeFailed(message);
				break;
			default:
				break;
		}
	}
}
