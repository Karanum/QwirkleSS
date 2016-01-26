package ss.qwirkle.common.ui;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import ss.qwirkle.common.Board;
import ss.qwirkle.common.Game;
import ss.qwirkle.common.Move;
import ss.qwirkle.common.player.HumanPlayer;
import ss.qwirkle.common.player.Player;
import ss.qwirkle.common.tiles.Color;
import ss.qwirkle.common.tiles.Shape;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;
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
	
	/**
	 * Creates a new TUI object with reference to the Game.
	 */
	//@ requires game != null;
	public TUI(Game game) {
		this.game = game;
		running = true;
		in = new BufferedReader(new InputStreamReader(System.in));
		
		System.out.println("=-=-= Qwirkle TUI =-=-=");
	}
	
	/**
	 * Starts polling for user input.
	 * To make use of multithreading, call start() instead.
	 */
	@Override
	public void run() {
		showCommandPrompt();
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
		if (running) {
			System.out.println("\nEnter your command (or 'help' for a list of commands):");
		}
	}
	
	/**
	 * Updates the game board shown by the UI to its most recent state.
	 */
	@Override
	public void update() {
		printGame();
		showCommandPrompt();
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
			System.out.println("\nTiles in bag: " + game.getBag().getSize());
			System.out.println("\n");
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
		if (game.getLocalPlayer() != null) {
			move = game.getLocalPlayer().getCurrentMove().orElse(new Move());
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
			int firstChar = (i / 26) - 1;
			int secondChar = i % 26;
			if (firstChar < 0) {
				markerLine += " ";
			} else {
				markerLine += (char) (firstChar + 65);
			}
			markerLine += (char) (secondChar + 65);
			markerLine += " " + TILE_DELIM;
			borderLine += LINE_DELIM + CORNER;
		}
		System.out.println(markerLine);
		System.out.println(borderLine);
	}
	
	/**
	 * Prints the scores of all players on the screen.
	 */
	private void printScores() {
		HumanPlayer localPlayer = game.getLocalPlayer();
		System.out.println("Your score: " + localPlayer.getScore());
		
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
		HumanPlayer player = game.getLocalPlayer();
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
				case "stop":
					running = false;
					break;
				case "help":
					showHelp();
					break;
				default:
					System.out.println("Unknown command! Type 'help' for a list of commands");
			}
		}
	}
	
	/**
	 * Tries to trade tiles by scanning the user input for tile IDs.
	 */
	private void tradeTiles(String[] args) {
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
		
		game.getLocalPlayer().tradeTiles(tiles);
	}
	
	/**
	 * Breaks down user input for the MOVE command and executes it.
	 */
	//@ requires args != null;
	private void parsePlaceTile(String[] args) {
		if (game.getLocalPlayer().getCurrentMove().orElse(null) == null) {
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
	private void placeTile(int handIndex, int x, int y) {
		Board board = game.getBoard();
		Move move = game.getLocalPlayer().getCurrentMove().orElse(new Move());
		Range xRange = new Range(board.getXRange());
		Range yRange = new Range(board.getYRange());
		if (!board.isEmpty() || !move.getTiles().isEmpty()) {
			xRange.setMin(Math.min(xRange.getMin(), move.getXRange().getMin()) - 1);
			yRange.setMin(Math.min(yRange.getMin(), move.getYRange().getMin()) - 1);
		}
		try {
			game.getLocalPlayer().makeMove(handIndex - 1, x + xRange.getMin(), y + yRange.getMin());
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
		char[] chars = input.toCharArray();
		for (char c : chars) {
			if (c < 'A' || c > 'Z') {
				System.out.println("Only use uppercase A-Z for column names!");
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
		Move m = game.getLocalPlayer().getCurrentMove().orElse(null);
		if (m == null) {
			System.out.println("It's not your turn yet!");
			return;
		}
		if (m.getTiles().size() == 0) {
			System.out.println("You have to place at least 1 tile!");
			return;
		}
		
		try {
			game.getLocalPlayer().finishMove();
		} catch (InvalidMoveException e) {
			System.out.println("The move cannot be finished like this!");
		}
	}
	
	/**
	 * Tells the local player to discard their current move and start over.
	 */
	private void resetMove() {
		if (game.getLocalPlayer().getCurrentMove().orElse(null) == null) {
			System.out.println("It's not your turn yet!");
			return;
		}
		game.getLocalPlayer().resetMove();
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
		System.out.printf("%-25s - %s\n", "STOP", "Quit the current game");
		System.out.printf("%-25s - %s\n", "HELP", "Shows a list of available commands");
	}
}
