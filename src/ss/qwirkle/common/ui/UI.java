package ss.qwirkle.common.ui;

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
	 * Redraws the game elements on the screen.
	 */
	public void update();
}
