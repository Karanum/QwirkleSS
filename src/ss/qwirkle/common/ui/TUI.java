package ss.qwirkle.common.ui;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import ss.qwirkle.common.Board;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.controller.SingleplayerGame;
import ss.qwirkle.common.controller.Game;
import ss.qwirkle.common.controller.Game.GameEndCause;
import ss.qwirkle.common.player.HumanPlayer;
import ss.qwirkle.common.player.Player;
import ss.qwirkle.common.player.ai.BasicBehaviour;
import ss.qwirkle.common.tiles.Color;
import ss.qwirkle.common.tiles.Shape;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;
import ss.qwirkle.util.PlayerScoreComparator;
import ss.qwirkle.util.Range;


/**
 * A textual user interface for the Qwirkle game.
 * @author Karanum
 */
public class TUI implements UI {

	private static final String CORNER = "+";
	private static final String LINE_DELIM = "----";
	private static final String EMPTY_LINE_DELIM = "    ";
	private static final String TILE_DELIM = "|";
	private static final String EMPTY_TILE_DELIM = " ";
	
	//@ private invariant game != null;
	//@ private invariant in != null;
	private Game game;
	private boolean running;
	private BufferedReader in;
	private List<String> queuedMessages;
	
	/**
	 * Creates a new TUI object with reference to the Game.
	 */
	//@ requires game != null;
	public TUI(Game game) {
		this.game = game;
		running = true;
		in = new BufferedReader(new InputStreamReader(System.in));
		queuedMessages = new ArrayList<String>();
		
		System.out.println("=-=-= Qwirkle TUI =-=-=");
	}
	
	/**
	 * Starts polling for user input.
	 */
	@Override
	public void run() {
		while (running) {
			try {
				while (in.ready()) {
					String input = in.readLine();
					parseInput(input);
				}
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
	
	public void stop() {
		running = false;
	}
	
	/**
	 * Shows a message that asks for user input.
	 */
	private void showCommandPrompt() {
		synchronized (this) {
			if (running) {
				System.out.println("\nEnter your command (or 'help' for a list of commands):");
			}
		}
	}
	
	/**
	 * Updates the game board shown by the UI to its most recent state.
	 */
	@Override
	public void update() {
		synchronized (this) {
			printGame();
			showCommandPrompt();
		}
	}
	
	/**
	 * Helper function to determine what character to use for each Shape.
	 */
	//@ requires shape != null;
	//@ pure
	private String getShape(Shape shape) {
		switch (shape) {
			case CIRCLE:
				return "o";
			case CROSS:
				return "x";
			case DIAMOND:
				return "d";
			case SQUARE:
				return "s";
			case STAR:
				return "*";
			case CLOVER:
				return "+";
			default:
				return "";
		}
	}
	
	/**
	 * Helper function to determine what character to use for each Color.
	 */
	//@ requires color != null;
	//@ pure
	private String getColor(Color color) {
		return String.valueOf(color.toInt() + 1);
	}
	
	/**
	 * Helper function to determine what string to use to represent a tile.
	 * @param tile The tile to represent
	 */
	//@ requires tile != null;
	//@ pure
	private String getTileString(Tile tile) {
		return getShape(tile.getShape()) + getColor(tile.getColor());
	}
	
	/**
	 * Prints the game board and all related aspects.
	 */
	private void printGame() {
		printBoard();
		if (game.getLocalPlayer() != null) {
			System.out.println("\n");
			printScores();
			if (game instanceof SingleplayerGame) {
				System.out.println("\nTiles in bag: " + 
									((SingleplayerGame) game).getBag().getSize());
			}
			System.out.println("");
			
			List<String> messages = new ArrayList<String>(queuedMessages);
			queuedMessages.clear();
			for (String message : messages) {
				System.out.println(message);
			}
			
			System.out.println("");
			printHand();
		}
	}
	
	/**
	 * Prints the game board on the screen.
	 */
	private void printBoard() {
		System.out.println("\n");
		Board board = game.getBoard();
		Move move = new Move();
		if (game.getLocalPlayer() != null && game.getLocalPlayer() instanceof HumanPlayer) {
			HumanPlayer p = (HumanPlayer) game.getLocalPlayer();
			move = p.getCurrentMove().orElse(new Move());
		}
		Range xRange = new Range(board.getXRange());
		Range yRange = new Range(board.getYRange());
		if (!board.isEmpty() || !move.getTiles().isEmpty()) {
			xRange.setMin(Math.min(xRange.getMin(), move.getXRange().getMin()) - 1);
			xRange.setMax(Math.max(xRange.getMax(), move.getXRange().getMax()) + 1);
			yRange.setMin(Math.min(yRange.getMin(), move.getYRange().getMin()) - 1);
			yRange.setMax(Math.max(yRange.getMax(), move.getYRange().getMax()) + 1);
		}
		
		printColumnMarkers(xRange);
		for (int i = 0; i < yRange.forEach().size(); ++i) {
			String tileLine = String.format("%3d ", i + 1) + TILE_DELIM;
			String borderLine = LINE_DELIM + CORNER;
			int y = yRange.getMin() + i;
			for (int j = 0; j < xRange.forEach().size(); ++j) {
				int x = xRange.getMin() + j;
				Tile tile = board.getTile(x, y).orElse(move.getTile(x, y).orElse(null));
				if (tile == null) {
					tileLine += EMPTY_LINE_DELIM;
					if (board.hasTile(x + 1, y) || move.hasTile(x + 1, y)) {
						tileLine += TILE_DELIM;
					} else {
						tileLine += EMPTY_TILE_DELIM;
					}
					
					if (board.hasTile(x, y + 1) || move.hasTile(x, y + 1)) {
						borderLine += LINE_DELIM;
					} else {
						borderLine += EMPTY_LINE_DELIM;
					}
				} else {
					String delimChar = " ";
					if (move.hasTile(x, y)) {
						delimChar = "-";
					}
					tileLine += delimChar + getTileString(tile) + delimChar + TILE_DELIM;
					borderLine += LINE_DELIM;
				}
				borderLine += CORNER;
			}
			System.out.println(tileLine);
			System.out.println(borderLine);
		}
	}
	
	/**
	 * Prints markers above all of the columns on the board.
	 * @param xRange The x range of the board
	 */
	//@ requires xRange != null;
	private void printColumnMarkers(Range xRange) {
		String markerLine = EMPTY_LINE_DELIM + TILE_DELIM;
		String borderLine = LINE_DELIM + CORNER;
		for (int i = 0; i < xRange.forEach().size(); ++i) {
			markerLine += " ";
			String column = makeColumn(i);
			if (column.length() < 2) {
				column = " " + column;
			}
			markerLine += column;
			markerLine += " " + TILE_DELIM;
			borderLine += LINE_DELIM + CORNER;
		}
		System.out.println(markerLine);
		System.out.println(borderLine);
	}
	
	private String makeColumn(int x) {
		String result = "";
		int firstChar = (x / 26) - 1;
		int secondChar = x % 26;
		if (firstChar >= 0) {
			result += (char) (firstChar + 65);
		}
		result += (char) (secondChar + 65);
		return result;
	}
	
	/**
	 * Prints the scores of all players on the screen.
	 */
	private void printScores() {
		Player localPlayer = game.getLocalPlayer();
		if (game.getLocalPlayer() != null) {
			System.out.println("Your score: " + localPlayer.getScore());
		}
		
		List<Player> players = game.getPlayers();
		for (Player player : players) {
			if (player != localPlayer) {
				System.out.println(player.getName() + "'s score: " + player.getScore());
			}
		}
	}
	
	/**
	 * Prints the local player's hand on the screen.
	 */
	private void printHand() {
		if (game.getLocalPlayer() == null || !(game.getLocalPlayer() instanceof HumanPlayer)) {
			return;
		}
		
		HumanPlayer player = (HumanPlayer) game.getLocalPlayer();
		List<Tile> hand = player.getHand();
		String delimLine = CORNER;
		String tileLine = TILE_DELIM;
		String idLine = EMPTY_TILE_DELIM;
		int handId = 1;
		for (Tile tile : hand) {
			delimLine += LINE_DELIM + CORNER;
			tileLine += " " + getTileString(tile) + " " + TILE_DELIM;
			idLine += " " + handId + "   ";
			++handId;
		}
		System.out.println("Your hand:");
		System.out.println(delimLine + "\n" + tileLine + "\n" + delimLine + "\n" + idLine);
	}

	/**
	 * Checks user input and executes the correct commands.
	 */
	//@ requires input != null;
	private void parseInput(String input) {
		String[] words = input.split(" ");
		if (words.length > 0) {
			String command = words[0].toLowerCase();
			switch (command) {
				case "move":
					parsePlaceTile(words);
					break;
				case "end":
					endTurn();
					break;
				case "reset":
					resetMove();
					break;
				case "trade":
					tradeTiles(words);
					break;
				case "hint":
					giveHint();
					break;
				case "stop":
					game.stop(GameEndCause.ERROR);
					stop();
					break;
				case "help":
					showHelp();
					break;
				default:
					System.out.println("Unknown command! Type 'help' for a list of commands");
			}
		}
	}
	
	private void giveHint() {
		if (game.getLocalPlayer() == null || !(game.getLocalPlayer() instanceof HumanPlayer)) {
			System.out.println("Can only use this when there's a human player!");
			return;
		}
		
		HumanPlayer p = (HumanPlayer) game.getLocalPlayer();
		Move currentMove = p.getCurrentMove().orElse(null);
		if (currentMove != null && !currentMove.getTiles().isEmpty()) {
			System.out.println("I only give hints at the start of your turn!");
			return;
		}
		
		Move move = new BasicBehaviour()
						.getPossibleMove(game.getBoard(), game.getLocalPlayer().getHand());
		if (move.getTiles().isEmpty()) {
			System.out.println("No moves possible! Trade away!");
			return;
		}
		Tile tile = move.getTiles().get(0);
		int x = tile.getX() - game.getBoard().getXRange().getMin() + 1;
		int y = tile.getY() - game.getBoard().getYRange().getMin() + 1;
		String tileString = getTileString(tile);
		System.out.println("You could place " + tileString + " at " + makeColumn(x - 1) + y);
	}
	
	/**
	 * Tries to trade tiles by scanning the user input for tile IDs.
	 */
	private void tradeTiles(String[] args) {
		if (game.getLocalPlayer() == null || !(game.getLocalPlayer() instanceof HumanPlayer)) {
			System.out.println("Can only use this when there's a human player!");
			return;
		}
		
		if (game.getBoard().isEmpty()) {
			System.out.println("You may not trade tiles while the board is empty!");
			return;
		}
		
		List<Tile> tiles = new ArrayList<Tile>();
		for (int i = 1; i < args.length; ++i) {
			try {
				int handId = Integer.parseInt(args[i]);
				tiles.add(game.getLocalPlayer().getHand().get(handId - 1));
			} catch (NumberFormatException e) {
				System.out.println("Argument is not a number: " + args[i]);
				return;
			}
		}
		
		((HumanPlayer) game.getLocalPlayer()).tradeTiles(tiles);
	}
	
	/**
	 * Breaks down user input for the MOVE command and executes it.
	 */
	//@ requires args != null;
	//@ requires game.getLocalPlayer() != null && game.getLocalPlayer() instanceof HumanPlayer;
	private void parsePlaceTile(String[] args) {
		HumanPlayer p = (HumanPlayer) game.getLocalPlayer();
		if (p.getCurrentMove().orElse(null) == null) {
			System.out.println("It's not your turn yet!");
			return;
		}
		if (args.length < 4) {
			System.out.println("Not enough arguments! Usage: MOVE (tile) (column) (row)");
			return;
		}
		
		int handIndex = 0;
		try {
			handIndex = Integer.parseInt(args[1]);
		} catch (NumberFormatException e) {
			System.out.println("First argument must be a number!");
		}
		if (handIndex < 0 || handIndex > 6) {
			System.out.println("Unknown tile number: " + args[1]);
			return;
		}
		
		int x = parseColumn(args[2]);
		int y = parseRow(args[3]);
		if (y < 0 || x < 0) {
			System.out.println("Hm?");
			return;
		} else {
			placeTile(handIndex, x, y);
		}
	}
	
	/**
	 * Adds a tile to the local player's current move.
	 * @param handIndex The index of the tile in the player's hand
	 * @param x The x position on the board
	 * @param y The y position on the board
	 */
	//@ requires game.getLocalPlayer() != null && game.getLocalPlayer() instanceof HumanPlayer;
	private void placeTile(int handIndex, int x, int y) {
		HumanPlayer p = (HumanPlayer) game.getLocalPlayer();
		Board board = game.getBoard();
		Move move = p.getCurrentMove().orElse(new Move());
		Range xRange = new Range(board.getXRange());
		Range yRange = new Range(board.getYRange());
		if (!board.isEmpty() || !move.getTiles().isEmpty()) {
			xRange.setMin(Math.min(xRange.getMin(), move.getXRange().getMin()) - 1);
			yRange.setMin(Math.min(yRange.getMin(), move.getYRange().getMin()) - 1);
		}
		try {
			p.makeMove(handIndex - 1, x + xRange.getMin(), y + yRange.getMin());
			update();
		} catch (InvalidMoveException e) {
			System.out.println("That move is not allowed!");
		}
	}
	
	/**
	 * Translates user input into a column number.
	 */
	//@ requires input != null;
	private int parseColumn(String input) {
		int result = -1;
		char[] chars = input.toUpperCase().toCharArray();
		for (char c : chars) {
			if (c < 'A' || c > 'Z') {
				System.out.println("Only use A-Z for column names!");
				return -1;
			}
			result = (result + 1) * 26;
			result += Character.getNumericValue(c) - 10;
		}
		return result;
	}
	
	/**
	 * Translates user input into a row number.
	 */
	//@ requires input != null;
	private int parseRow(String input) {
		int result = -1;
		try {
			result = Integer.parseInt(input) - 1;
		} catch (NumberFormatException e) {
			System.out.println("Only use digits for row numbers!");
		}
		return result;
	}
	
	/**
	 * Tells the local player to end their turn.
	 */
	private void endTurn() {
		if (game.getLocalPlayer() == null || !(game.getLocalPlayer() instanceof HumanPlayer)) {
			System.out.println("Can only use this when there's a human player!");
			return;
		}
		
		HumanPlayer p = (HumanPlayer) game.getLocalPlayer();
		Move m = p.getCurrentMove().orElse(null);
		if (m == null) {
			System.out.println("It's not your turn yet!");
			return;
		}
		if (m.getTiles().size() == 0) {
			System.out.println("You have to place at least 1 tile!");
			return;
		}
		
		try {
			p.finishMove();
		} catch (InvalidMoveException e) {
			System.out.println("The move cannot be finished like this!");
		}
	}
	
	/**
	 * Tells the local player to discard their current move and start over.
	 */
	private void resetMove() {
		if (game.getLocalPlayer() == null || !(game.getLocalPlayer() instanceof HumanPlayer)) {
			System.out.println("Can only use this when there's a human player!");
			return;
		}
		
		HumanPlayer p = (HumanPlayer) game.getLocalPlayer();
		if (p.getCurrentMove().orElse(null) == null) {
			System.out.println("It's not your turn yet!");
			return;
		}
		p.resetMove();
		update();
	}
	
	/**
	 * Prints a list of commands and their descriptions on the screen.
	 */
	private void showHelp() {
		System.out.println("\nList of available commands:");
		System.out.printf("%-25s - %s\n", "MOVE (tile) (column) (row)", 
								"Place a tile (e.g. MOVE 3 D 5)");
		System.out.printf("%-25s - %s\n", "END", "End your move and finishes placing the tiles");
		System.out.printf("%-25s - %s\n", "RESET", "Return the tiles you placed to your hand");
		System.out.printf("%-25s - %s\n", "TRADE (tiles...)", 
								"Trade some of the tiles in your hand (e.g. TRADE 1 2 5 6)");
		System.out.printf("%-25s - %s\n", "HINT", "Gives a hint about a possible move");
		System.out.printf("%-25s - %s\n", "STOP", "Quit the current game");
		System.out.printf("%-25s - %s\n", "HELP", "Shows a list of available commands");
	}

	/**
	 * Shows a game over message with the game results.
	 */
	@Override
	public void gameOver(GameEndCause cause) {
		synchronized (this) {
			System.out.println("\n========== GAME OVER ==========");
			if (cause == GameEndCause.EMPTY_HAND) {
				System.out.println("A player was out of tiles! The game has ended!");
			} else if (cause == GameEndCause.NO_MOVES) {
				System.out.println("No more moves possible! The game has ended!");
			} else if (cause == GameEndCause.UNSPECIFIED) {
				System.out.println("The game has ended!");
			} else {
				System.out.println("The game has been ended prematurely!");
			}
			System.out.println("\nScores:");
			
			List<Player> players = game.getPlayers();
			Collections.sort(players, new PlayerScoreComparator());
			Collections.reverse(players);
			for (Player p : players) {
				System.out.println("- " + p.getName() + "'s points: " + p.getScore());
			}
			
			if (cause != GameEndCause.ERROR) {
				if (players.size() > 1 && players.get(0).getScore() > players.get(1).getScore()) {
					System.out.println("\nPlayer " + players.get(0).getName() + " has won!");
				} else {
					System.out.println("\nIt's a draw!");
				}
			}
		}
	}

	/**
	 * Shows a message on the screen.
	 * @param message The message to show
	 */
	@Override
	public void showMessage(String message) {
		synchronized (this) {
			queuedMessages.add(message);
		}
	}
}
