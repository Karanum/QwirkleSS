package ss.qwirkle.client.ui;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import ss.qwirkle.client.Game;
import ss.qwirkle.client.tiles.Color;
import ss.qwirkle.client.tiles.Shape;

/**
 * A textual user interface for the Qwirkle game.
 * @author Karanum
 */
public class TUI implements UI {

	private Game game;
	private boolean running;
	private BufferedReader in;
	
	public TUI(Game game) {
		this.game = game;
		running = true;
		in = new BufferedReader(new InputStreamReader(System.in));
	}
	
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
	
	private String getShape(Shape shape) {
		String result = "??";
		//switch (shape) {
		//}
		return result;
	}
	
	private String getColor(Color color) {
		String result = "";
		return result;
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
				default:
			}
		}
	}
}
