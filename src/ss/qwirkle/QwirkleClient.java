package ss.qwirkle;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.UnknownHostException;

import ss.qwirkle.common.controller.ClientGame;
import ss.qwirkle.common.controller.SingleplayerGame;
import ss.qwirkle.common.player.AIPlayer;
import ss.qwirkle.common.player.HumanPlayer;
import ss.qwirkle.common.player.ai.BasicBehaviour;
import ss.qwirkle.common.ui.TUI;
import ss.qwirkle.network.Client;

/**
 * Main class for the client-side program.
 * @author Karanum
 */
public class QwirkleClient {
	
	public static void main(String[] args) {
		boolean running = true;
		while (running) {
			int gameType = 0;
			do { 
				gameType = queryGameType();
				System.out.println("");
			} while (gameType < 1 || gameType > 2);
			
			int numPlayers = 0;
			do {
				numPlayers = queryPlayerNum();
				System.out.println("");
			} while (numPlayers < 1 || numPlayers > 4);
			
			if (gameType == 1) {
				startSingleplayer(numPlayers);
			} else {
				startClient(numPlayers);
			}
			
			running = queryPlayAgain();
			System.out.println("");
		}
	}
	
	private static void startSingleplayer(int players) {
		String name = queryName(true);
		
		SingleplayerGame game = new SingleplayerGame();
		game.setup(new TUI(game));
		if (!name.isEmpty()) {
			game.addPlayer(new HumanPlayer(game, name));
		} else {
			game.addPlayer(new AIPlayer(game, "Player1", new BasicBehaviour()));
		}
		
		if (players == 1) {
			game.addPlayer(new AIPlayer(game, "Player2", new BasicBehaviour()));
			game.addPlayer(new AIPlayer(game, "Player3", new BasicBehaviour()));
			game.addPlayer(new AIPlayer(game, "Player4", new BasicBehaviour()));
		} else {
			for (int i = 0; i < players - 1; ++i) {
				game.addPlayer(new AIPlayer(game, "Player" + (i + 2), new BasicBehaviour()));
			}
		}
		game.start();
	}
	
	private static void startClient(int players) {		
		InetAddress hostname;
		int port;
		
		do {
			hostname = queryServerIP();
		} while (hostname == null);
		do {
			port = queryServerPort();
		} while (port < 0);
		
		ClientGame game = new ClientGame();
		Client client = new Client(game, hostname, port);
		client.start();
		game.setup(new TUI(game), client, players);
		game.start();
		
		try {
			client.join();
		} catch (InterruptedException e) {
			System.out.println("ERROR: Main thread has been interrupted!");
		}
	}
	
	private static int queryGameType() {
		BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
		String input = "";
		
		System.out.println("Welcome to Qwirkle Client! What kind of game do you want to play?");
		System.out.println("(1 = Singleplayer, 2 = Multiplayer)");
		try {
			input = in.readLine();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		try {
			int intInput = Integer.parseInt(input); 
			return intInput;
		} catch (NumberFormatException e) {
			System.out.println("Unknown input! Please enter 1 or 2!");
		}
		
		return -1;
	}
	
	private static int queryPlayerNum() {
		BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
		String input = "";
		
		System.out.println("How many players do you want to play with?");
		System.out.println("(1 = No preference, 2 = Two players, "
								+ "3 = Three players, 4 = Four players)");
		try {
			input = in.readLine();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		try {
			int intInput = Integer.parseInt(input); 
			return intInput;
		} catch (NumberFormatException e) {
			System.out.println("Unknown input! Please enter 1-4!");
		}
		
		return -1;
	}
	
	private static boolean queryPlayAgain() {
		BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
		String input = "";
		
		System.out.println("\nWould you like to play again?");
		System.out.println("(y = Yes, n = No)");
		try {
			input = in.readLine();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return input.equalsIgnoreCase("y");
	}
	
	public static String queryName(boolean allowAi) {
		BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
		String input = "";
		
		String prompt = "Please enter your name";
		if (allowAi) {
			prompt += " (or leave empty for AI)";
		}
		prompt += ":";
		
		System.out.println(prompt);
		try {
			input = in.readLine();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return input;
	}
	
	private static InetAddress queryServerIP() {
		BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
		String input = "";
		
		System.out.println("Enter the server hostname:");
		try {
			input = in.readLine();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		try {
			return InetAddress.getByName(input);
		} catch (UnknownHostException e) {
			System.out.println("Unknown hostname! Please check your spelling and try again");
		}
		
		return null;
	}
	
	private static int queryServerPort() {
		BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
		String input = "";
		
		System.out.println("Enter the server port:");
		try {
			input = in.readLine();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		try {
			int intInput = Integer.parseInt(input); 
			return intInput;
		} catch (NumberFormatException e) {
			System.out.println("Unknown input! Please enter a valid port number!");
		}
		
		return -1;
	}
	
}
