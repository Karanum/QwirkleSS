package ss.qwirkle.network;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

import ss.qwirkle.common.controller.ServerGame;
import ss.qwirkle.common.ui.UI;

/**
 * Server class that handles connections with remote clients.
 * @author Karanum
 */
public class Server {

	//@ private invariant serverUI != null;
	//@ private invariant threads != null;
	//@ private invariant games != null;
	//@ private invariant names != null;
    private UI serverUI;
    private List<ClientHandler> threads;
    private List<ServerGame> games;
    private List<String> names;
    
    //@ private invariant queue2Players != null;
    //@ private invariant queue3Players != null;
    //@ private invariant queue4Players != null;
    private List<ClientHandler> queue2Players;
    private List<ClientHandler> queue3Players;
    private List<ClientHandler> queue4Players;
    
    private int port;
    
   	/**
   	 * Creates a new server and runs it on the specified port.
   	 * @param ui The user interface for the server
   	 * @param port The port to run the server on
   	 */
    //@ requires ui != null;
    //@ requires port > 0;
    public Server(UI ui, int port) {
        this.port = port;
        serverUI = ui;
        names = new ArrayList<String>();
        games = new ArrayList<ServerGame>();
        threads = new ArrayList<ClientHandler>();
        queue2Players = new ArrayList<ClientHandler>();
        queue3Players = new ArrayList<ClientHandler>();
        queue4Players = new ArrayList<ClientHandler>();
    }
    
    /**
     * Listens on the server port for clients trying to connect.
     * Each connecting player will get its own ClientHandler object.
     * @see ss.qwirkle.network.ClientHandler ClientHandler
     */
    public void run() {
    	(new Thread(serverUI)).start();
    	
		ServerSocket server = null;
		try {
			server = new ServerSocket(port);
		} catch (IOException e) {
			System.out.println("ERROR: Could not start a server on port " + port);
		}
		
    	while (server != null) {
    		try {
    			Socket client = server.accept();
    			ClientHandler handler = new ClientHandler(this, client);
    			handler.start();
    			addHandler(handler);
    		} catch (IOException e) {
    			System.out.println("ERROR: A client failed to connect");
    		}
    	}	
    }
    
    /**
     * Sends a message to all connected clients.
     * @param message The message to send
     */
    //@ requires message != null;
    public void broadcast(String message) {
        for (ClientHandler thread : threads) {
        	if (thread != null) {
        		thread.sendMessage(message);
        	}
        }
    }
    
    /**
     * Returns the server UI.
     */
    //@ pure
    public UI getUI() {
    	return serverUI;
    }
    
    /**
     * Add a ClientHandler to the collection of ClientHandlers.
     * @param handler ClientHandler that will be added
     */
    //@ requires handler != null;
    public void addHandler(ClientHandler handler) {
        threads.add(handler);
    }
    
    /**
     * Remove a ClientHandler from the collection of ClientHanlders. 
     * @param handler ClientHandler that will be removed
     */
    //@ requires handler != null;
    public void removeHandler(ClientHandler handler) {
    	if (handler.getPlayerName() != null) {
    		names.remove(handler.getPlayerName());
    	}
    	queue2Players.remove(handler);
    	queue3Players.remove(handler);
    	queue4Players.remove(handler);
        threads.remove(handler);
    }
    
    public void registerName(String name) {
    	names.add(name);
    }
    
    public boolean isNameTaken(String name) {
    	return names.contains(name);
    }
    
    public void queueClient(ClientHandler handler, List<Integer> queues) {
    	if (queues.contains(2)) {
    		queue2Players.add(handler);
    		if (queue2Players.size() >= 2) {
    			startGame(queue2Players, 2);
    		}
    	}
    	if (queues.contains(3)) {
    		queue3Players.add(handler);
    		if (queue3Players.size() >= 3) {
    			startGame(queue3Players, 3);
    		}
    	}
    	if (queues.contains(4)) {
    		queue4Players.add(handler);
    		if (queue4Players.size() >= 4) {
    			startGame(queue4Players, 4);
    		}
    	}
    	handler.serverQueue(queues);
    }
    
    private void startGame(List<ClientHandler> queue, int players) {
    	List<ClientHandler> playerList = new ArrayList<ClientHandler>();
    	for (int i = 0; i < players; ++i) {
    		playerList.add(queue.remove(0));
    	}
    	ServerGame game = new ServerGame(playerList);
    	for (ClientHandler p : playerList) {
    		p.setGame(game);
    	}
    	
    	games.add(game);
    	game.setup(serverUI);
    	game.start();
    }
    
}
