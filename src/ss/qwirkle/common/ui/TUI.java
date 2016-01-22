package ss.qwirkle.common.ui;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.List;

import ss.qwirkle.common.Board;
import ss.qwirkle.common.Game;
import ss.qwirkle.common.player.HumanPlayer;
import ss.qwirkle.common.tiles.Color;
import ss.qwirkle.common.tiles.Shape;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.util.Range;


/**
 * A textual user interface for the Qwirkle game.
 * @author Karanum
 */
public class TUI implements UI {

	private static final String LINE_DELIM = "+----+";
	private static final String TILE_DELIM = "|";
	
	private Game game;
	private boolean running;
	private BufferedReader in;
	
	public TUI(Game game) {
		this.game = game;
		running = true;
		in = new BufferedReader(new InputStreamReader(System.in));
	}
	
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
	
	@Override
	public void update() {
		printGame();
	}
	
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
	
	private String getColor(Color color) {
		return String.valueOf(color.toInt() + 1);
	}
	
	private String getTileString(Tile tile) {
		return getShape(tile.getShape()) + getColor(tile.getColor());
	}
	
	private void printGame() {
		printBoard();
		printHand();
	}
	
	private void printBoard() {
		Board board = game.getBoard();
		Range xRange = board.getXRange();
		Range yRange = board.getYRange();
	}
	
	private void printHand() {
		HumanPlayer player = game.getLocalPlayer();
		List<Tile> hand = player.getHand();
		String delimLine = String.valueOf(LINE_DELIM.charAt(0));
		String tileLine = TILE_DELIM;
		for (Tile tile : hand) {
			delimLine += LINE_DELIM.substring(1);
			tileLine += " " + getTileString(tile) + " " + TILE_DELIM;
		}
		System.out.println("Your hand:");
		System.out.println(delimLine + "\n" + tileLine + "\n" + delimLine);
	}

	private void parseInput(String input) {
		String[] words = input.split(" ");
		if (words.length > 0) {
			String command = words[0].toLowerCase();
			switch (command) {
				case "move":
					break;
				case "end":
					break;
				case "trade":
					break;
				case "stop":
					running = false;
					break;
				default:
			}
		}
	}
}
