package ss.qwirkle.network;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import nl.utwente.ewi.qwirkle.net.IProtocol;
import nl.utwente.ewi.qwirkle.net.IProtocol.Feature;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.controller.SingleplayerGame;
import ss.qwirkle.common.controller.Game.GameEndCause;
import ss.qwirkle.common.controller.ServerGame;
import ss.qwirkle.common.player.Player;
import ss.qwirkle.common.tiles.Tile;

public class ClientHandler extends Thread {
	
	//@ private invariant server != null;
	//@ private invariant socket != null;
	//@ private invariant in != null;
	//@ private invariant out != null;
    private Server server;
    private Socket socket;
    private BufferedReader in;
    private BufferedWriter out;
    
    private ServerGame game;
    private String clientName;
    private boolean running;
	
	public ClientHandler(Server server, Socket sock) throws IOException {
		this.server = server;
		socket = sock;
		game = null;
		clientName = null;
		running = false;
		
    	in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
    	out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
	}
	
    private void announceLeave(String reason) {
        server.removeHandler(this);
        server.getUI().showMessage(String.format("[Disconnect: %s, Reason: %s]", 
        							socket.getInetAddress().getHostAddress(), reason));
    }
    
    public void announceJoin() {
        server.getUI().showMessage(String.format("[Connect: %s]", 
        							socket.getInetAddress().getHostAddress()));
    }
    
    public String getPlayerName() {
    	return clientName;
    }
    
    public void sendMessage(String message) {
        try {
        	out.write(message);
        	out.newLine();
        	out.flush();
        } catch (IOException e) {
        	announceLeave("Connection lost");
        }
    }
    
    public void run() {
    	announceJoin();
    	running = true;
    	while (running) {
    		try {
				if (in.ready()) {
					String input = in.readLine();
					parseCommand(input);
				}
			} catch (IOException e) {
				announceLeave("Connection lost");
			}
    	}
    }
    
    public void drawPlayerTile(List<Tile> tiles) {
    	String message = IProtocol.SERVER_DRAWTILE;
    	for (Tile t : tiles) {
    		message += " " + t.toInt();
    	}
    	send(message);
    } //TODO: Call this function
    
    public void putMove(Move m) {
    	String message = IProtocol.SERVER_MOVE_PUT;
		for (Tile t : m.getTiles()) {
			message += String.format(" %d@%d,%d", t.toInt(), t.getX(), t.getY());
		}
		send(message);
    } //TODO: Call this function
    
    public void sendError(IProtocol.Error error, String msg) {
    	String message = IProtocol.SERVER_ERROR;
    	message += " " + error + " " + msg;
    	send(message);
    }
    
    public void winMessage(List<Player> players, SingleplayerGame.GameEndCause cause) {
    	String message = IProtocol.SERVER_GAMEEND + " ";
    	message += cause == GameEndCause.ERROR ? "ERROR" : "WIN";
    	for (Player player : players) {
    		int score = player.getScore();
    		message += " " + score + "," + player.getName();
    	}
    	send(message);
    } //TODO: Call this function
    
    public void gameStart(List<Player> players) {
    	String message = IProtocol.SERVER_GAMESTART;
    	for (Player player : players) {
    		String name = player.getName();
    		message += " " + name;
    	}
    	send(message);
    } //TODO: Call this function
    
    public void identifyPlayer(List<IProtocol.Feature> features) {
    	String message = IProtocol.SERVER_IDENTIFY;
		message += " ";
		Iterator<IProtocol.Feature> iterator = features.iterator();
		while (iterator.hasNext()) {
			message += iterator.next();
			if (iterator.hasNext()) {
				message += ",";
			}
		}
		send(message);
    }
    
    public void tradeMove(int amount) {
    	String message = IProtocol.SERVER_MOVE_TRADE;
    	message += " " + amount;
    	send(message);
    } //TODO: Call this function
    
    public void currentTurn(Player player) {
    	String message = IProtocol.SERVER_TURN;
    	message += " " + player.getName();
    	send(message);
    } //TODO: Call this function
    
    public void turnPassed(Player player) {
    	String message = IProtocol.SERVER_PASS;
    	message += " " + player.getName();
    	send(message);
    } //TODO: Call this function
    
    public void serverQueue(List<Integer> numbersOfPlayers) {
    	String message = IProtocol.SERVER_QUEUE;
		message += " ";
		Iterator<Integer> iterator = numbersOfPlayers.iterator();
		while (iterator.hasNext()) {
			message += iterator.next();
			if (iterator.hasNext()) {
				message += ",";
			}
		}
		send(message);
	}
    
    private void send(String message) {
		try {
			out.write(message);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
    
    public void parseCommand(String message) {
		String[] args = message.split(" ");
		switch (args[0]) {
			case IProtocol.CLIENT_MOVE_PUT:
				break;
			case IProtocol.CLIENT_IDENTIFY:
				identifyPlayer(args);
				break;
			case IProtocol.CLIENT_MOVE_TRADE:
				break;
			case IProtocol.CLIENT_QUIT:
				break;
			case IProtocol.SERVER_QUEUE:
				break;
		}
	}
    
    /**
     * Command executor for CLIENT_IDENTIFY.
     */
    public void identifyPlayer(String[] args) {
    	if (args.length < 2) {
    		sendError(IProtocol.Error.INVALID_PARAMETER, "Missing parameter");
    		return;
    	}
    	
    	String name = args[1];
    	if (!name.matches(IProtocol.NAME_REGEX)) {
    		sendError(IProtocol.Error.NAME_INVALID, "Invalid name");
    		return;
    	}
    	if (server.isNameTaken(name)) {
			sendError(IProtocol.Error.NAME_USED, "Name is already taken");
			return;
    	}
    	
    	clientName = name;
    	server.registerName(name);
    	identifyPlayer(new ArrayList<Feature>());
    }
}
