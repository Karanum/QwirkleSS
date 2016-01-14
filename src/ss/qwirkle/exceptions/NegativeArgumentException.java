package ss.qwirkle.exceptions;

/**
 * Exception thrown when a negative argument is provided where this is not acceptable.
 * @author Karanum
 */
public class NegativeArgumentException extends Exception {

	private static final long serialVersionUID = 1L;

	@Override
	public String getMessage() {
		return "ERROR: A negative parameter was passed where this was not permitted";
	}
	
}
