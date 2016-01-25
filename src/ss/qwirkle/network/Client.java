package ss.qwirkle.network;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.Iterator;
import java.util.List;

import nl.utwente.ewi.qwirkle.net.IProtocol;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.tiles.Tile;
/**
 * 
 * @author Dylan
 *
 */

public class Client extends Thread {
	
	private Socket sock;
	private BufferedReader in;
	private BufferedWriter out;
	
	public Client(InetAddress host, int port) throws IOException {
		try {
			sock = new Socket(host, port);
	    	in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
	    	out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
        } catch (IOException e) {
            System.out.println("ERROR: could not create a socket on " + host
                    + " and port " + port);
		}	
	}
	/** send a message to a ClientHandler. */
	public void sendMessage(String message) {
		try {
			out.write(message);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			System.out.println("Connection has been lost.");
			shutdown();
		}
    }
	/** close the socket connection. */
	public void shutdown() {
		try {
			sock.close();
			in.close();
			out.close();
			System.exit(0);
		} catch (IOException e) {
			e.printStackTrace();
		}	
	}
	public String readMessage(String message) {
		String response = null;
		try {
			BufferedReader input = new BufferedReader(new InputStreamReader(System.in));
			response = input.readLine();
		} catch (IOException e) {
		}
		return (response == null) ? "" : response;
	}
	public void sendMove(Move m) {
		String message = IProtocol.CLIENT_MOVE_PUT;
		for (Tile t : m.getTiles()) {
			message += String.format(" %d@%d,%d", t.toInt(), t.getX(), t.getY());
		}
		send(message);
	}
	public void tradeTile(int amount) {
		String message = IProtocol.SERVER_MOVE_TRADE;
		message += " " + amount;
		send(message);
	}
	public void tradeMove(List<Tile> tiles) {
		String message = IProtocol.CLIENT_MOVE_TRADE;
		for (Tile t: tiles) {
			message += " " + t.toInt();
		}
		send(message);
	}
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
		send(message);
	}
	public void quitPlayer() {
		String message = IProtocol.CLIENT_QUIT;
		send(message);
	}
	public void identifyPlayer(String name, List<IProtocol.Feature> features) {
		String message = IProtocol.CLIENT_IDENTIFY;
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
	
	private void send(String message) {
		try {
			out.write(message);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	public void parseCommands() {
		//startGame();
	}
}
