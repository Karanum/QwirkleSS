package ss.qwirkle.network;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

import nl.utwente.ewi.qwirkle.net.IProtocol;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.player.Player;
import ss.qwirkle.common.tiles.Tile;

public class Server {
    private static final String USAGE
            = "usage: " + Server.class.getName() + " <port>";

    /** Start een Server-applicatie op. */
    public static void main(String[] args) {
        if (args.length != 1) {
            System.out.println(USAGE);
            System.exit(0);
        }
        
        Server server = new Server(Integer.parseInt(args[0]));
        server.run();
        
    }


    private int port;
    private List<ClientHandler> threads;
    /** Constructs a new Server object. */
    public Server(int port) {
        this.port = port;
        threads = new ArrayList<ClientHandler>();
    }
    
    /**
     * Listens to a port of this Server if there are any Clients that 
     * would like to connect. For every new socket connection a new
     * ClientHandler thread is started that takes care of the further
     * communication with the Client.
     */
    public void run() {
		ServerSocket server = null;
		try {
			server = new ServerSocket(port);
		} catch (IOException e1) {
			e1.printStackTrace();
		}
    	while (server != null) {
    		try {
    			Socket client = server.accept();
    			ClientHandler handler = new ClientHandler(this, client);
    			handler.announce();
    			handler.start();
    			addHandler(handler);
    		} catch (IOException e) {
    			System.out.println("ERROR: could not create a socket on port " + port);
    		}
    	}	
    }
    
    public void print(String message) {
        System.out.println(message);
    }
    
    /**
     * Sends a message using the collection of connected ClientHandlers
     * to all connected Clients.
     * @param msg message that is send
     */
    public void broadcast(String msg) {
    	print(msg);
        for (ClientHandler thread : threads) {
        	if (thread != null) {
        		thread.sendMessage(msg);
        	}
        }
    }
    
    /**
     * Add a ClientHandler to the collection of ClientHandlers.
     * @param handler ClientHandler that will be added
     */
    public void addHandler(ClientHandler handler) {
        threads.add(handler);
    }
    
    /**
     * Remove a ClientHandler from the collection of ClientHanlders. 
     * @param handler ClientHandler that will be removed
     */
    public void removeHandler(ClientHandler handler) {
        threads.remove(handler);
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
    public void winMessage(List<Player> players, String result ) {
    	String message = IProtocol.SERVER_GAMEEND + " " + result;
    	for (Player player : players) {
    		int score = player.getScore();
    		message += " " + score + "," + player.getName();
    	}
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
}
