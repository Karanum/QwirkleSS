package ss.qwirkle.common.ui;

import ss.qwirkle.common.Game;

/**
 * UI interface that handles interaction with the user.
 * @author Karanum
 */
public interface UI extends Runnable {
	
	/**
	 * Start checking for user input.
	 */
	public void run();
	
	/**
	 * Stops the UI and cleans up the thread.
	 */
	public void stop();
	
	/**
	 * Redraws the game elements on the screen.
	 */
	public void update();
	
	/**
	 * Shows a game over message with the game results.
	 */
	public void gameOver(Game.GameEndCause cause);
}
