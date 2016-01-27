package ss.qwirkle.common.ui;

import ss.qwirkle.common.controller.SingleplayerGame;

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
	 * @param cause The cause of the game over
	 */
	//@ requires cause != null;
	public void gameOver(SingleplayerGame.GameEndCause cause);
	
	/**
	 * Shows a message on the screen.
	 * @param message The message to show
	 */
	//@ requires message != null;
	public void showMessage(String message);
}
