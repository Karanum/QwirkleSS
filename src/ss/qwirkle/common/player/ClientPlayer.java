package ss.qwirkle.common.player;

import ss.qwirkle.network.ClientHandler;

/**
 * A player on a server that is controlled by a client.
 * @author Karanum
 */
public class ClientPlayer extends Player {

	private ClientHandler handler;
	
	/**
	 * Creates a new ClientPlayer.
	 * @param handler The client handler corresponding to the player
	 * @param name The name of the player
	 */
	public ClientPlayer(ClientHandler handler, String name) {
		super(name);
		this.handler = handler;
	}
	
	/**
	 * Waits for the remote player to determine their move.
	 */
	@Override
	public void determineMove() {

	}

	/**
	 * Used by the network client to notify that the player's trade failed.
	 */
	//@ requires message != null;
	@Override
	public void tradeFailed(String message) {
		
	}

}
