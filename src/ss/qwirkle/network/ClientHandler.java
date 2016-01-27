package ss.qwirkle.network;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.Iterator;
import java.util.List;

import nl.utwente.ewi.qwirkle.net.IProtocol;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.controller.SingleplayerGame;
import ss.qwirkle.common.controller.Game.GameEndCause;
import ss.qwirkle.common.player.Player;
import ss.qwirkle.common.tiles.Tile;

public class ClientHandler extends Thread {
	
    private Server server;
    private BufferedReader in;
    private BufferedWriter out;
    private String clientName;
	
	public ClientHandler(Server server, Socket sock) throws IOException {
		this.server = server;
    	in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
    	out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
		
	}
    private void shutdown() {
        server.removeHandler(this);
        server.broadcast("[" + clientName + " has left]");
    }
    public void announce() throws IOException {
        clientName = in.readLine();
        server.broadcast("[" + clientName + " has entered]");
    }
    public void sendMessage(String message) {
        try {
        	out.write(message);
        	out.newLine();
        	out.flush();
        } catch (IOException e) {
        	shutdown();
        }
    }
    public void run() {
    	while (true) {
    		try {
    			String line = in.readLine();
    			if (line != null) {
    				server.broadcast(clientName + ": " + line);
    			}
    		} catch (IOException e) {
    			shutdown();
    		}
    	}
    }
    public void drawPlayerTile(List<Tile> tiles) {
    	String message = IProtocol.SERVER_DRAWTILE;
    	for (Tile t : tiles) {
    		message += " " + t.toInt();
    	}
    	send(message);
    	
    }
    public void putMove(Move m) {
    	String message = IProtocol.SERVER_MOVE_PUT;
		for (Tile t : m.getTiles()) {
			message += String.format(" %d@%d,%d", t.toInt(), t.getX(), t.getY());
		}
		send(message);
    }
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
    }
    public void gameStart(List<Player> players) {
    	String message = IProtocol.SERVER_GAMESTART;
    	for (Player player : players) {
    		String name = player.getName();
    		message += " " + name;
    	}
    	send(message);
    }
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
    }
    public void currentTurn(Player player) {
    	String message = IProtocol.SERVER_TURN;
    	message += " " + player.getName();
    	send(message);
    }
    public void turnPassed(Player player) {
    	String message = IProtocol.SERVER_PASS;
    	message += " " + player.getName();
    	send(message);
    }
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
    public void parseCommands(String message) {
		String[] args = message.split(" ");
		switch (args[0].toUpperCase()) {
			case IProtocol.CLIENT_MOVE_PUT:
				break;
			case IProtocol.CLIENT_IDENTIFY:
				break;
			case IProtocol.CLIENT_MOVE_TRADE:
				break;
			case IProtocol.CLIENT_QUIT:
				break;
			case IProtocol.SERVER_QUEUE:
				break;
		}
	}
}
