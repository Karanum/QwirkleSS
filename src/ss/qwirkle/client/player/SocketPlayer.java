package ss.qwirkle.client.player;

/**
 * A player that is controlled by a remote user over a socket.
 * @author Karanum
 */
public class SocketPlayer extends Player {
	
	/**
	 * Creates a new player with the given name.
	 * @param name The name of the new player
	 */
	//@ requires name != null;
	public SocketPlayer(String name) {
		super(name);
	}
	
	/**
	 * Waits for the remote player to determine their move.
	 */
	@Override
	public void determineMove() {
		
	}
	
}
