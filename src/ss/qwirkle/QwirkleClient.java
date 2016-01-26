package ss.qwirkle;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import ss.qwirkle.common.Game;
import ss.qwirkle.common.Game.GameType;
import ss.qwirkle.common.player.AIPlayer;
import ss.qwirkle.common.player.HumanPlayer;
import ss.qwirkle.common.player.ai.BasicBehaviour;
import ss.qwirkle.common.ui.TUI;

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
		Game.type = GameType.SINGLEPLAYER;
		String name = queryName(true);
		
		Game game = new Game();
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
		Game.type = GameType.CLIENT;
		
		//TODO: Implement client
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
	
	private static String queryName(boolean allowAi) {
		BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
		String input = "";
		
		String prompt = "Please enter your name";
		if (allowAi) {
			prompt += " (or empty for AI)";
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
	
}
