package ss.qwirkle.exceptions;

/**
 * Exception thrown when an invalid move is attempted.
 * @author Karanum
 */
public class InvalidMoveException extends Exception {

	private static final long serialVersionUID = 1L;
	
	@Override
	public String getMessage() {
		return "ERROR: This move is not allowed";
	}

}
