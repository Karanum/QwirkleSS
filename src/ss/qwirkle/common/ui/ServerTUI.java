package ss.qwirkle.common.ui;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import ss.qwirkle.common.controller.Game;
import ss.qwirkle.common.controller.Game.GameEndCause;

/**
 * Very bare UI for the server.
 * @author Karanum
 */
public class ServerTUI implements UI {

	private Game game;
	private BufferedReader in;
	private boolean running;
	
	//@ requires game != null;
	public ServerTUI(Game game) {
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
	public void stop() {
		running = false;
	}

	@Override
	public void update() {
		// Does nothing when used on the server UI, it's just that bare.
		// Seriously though, the server won't echo the board to itself. Too much clutter.
	}

	@Override
	public void gameOver(GameEndCause cause) {
		System.out.println("Game ended due to cause: " + cause);
	}

	@Override
	public void showMessage(String message) {
		System.out.println(message);
	}
	
	private void parseInput(String input) {
		if (input.equalsIgnoreCase("stop")) {
			game.stop(GameEndCause.ERROR);
			stop();
		} else {
			System.out.println("Unknown command. Server can only receive 'stop' command");
		}
	}

}
