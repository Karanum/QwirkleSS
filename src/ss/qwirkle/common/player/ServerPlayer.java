package ss.qwirkle.common.player;

/**
 * A player that is controlled by a remote user through a server.
 * The functions in this class should not have to be called at all by the client.
 * @author Karanum
 */
public class ServerPlayer extends Player {
	
	/**
	 * Creates a new player with the given name.
	 * @param name The name of the new player
	 */
	//@ requires name != null;
	public ServerPlayer(String name) {
		super(name);
	}
	
	/**
	 * Waits for the remote player to determine their move.
	 */
	@Override
	public void determineMove() {
		System.out.println("ERROR: Client tried to do a move for a remote player.");
	}

	/**
	 * Used by the network client to notify that the player's trade failed.
	 */
	//@ requires message != null;
	@Override
	public void tradeFailed(String message) {
		System.out.println("ERROR: Server sent a packet to the wrong player.");
	}

	/**
	 * Used by the network client to notify that the player's move failed.
	 */
	@Override
	public void moveFailed(String message) {
		System.out.println("ERROR: Server sent a packet to the wrong player.");
	}
	
}
