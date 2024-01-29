package exception;

import protocol.Protocol;

/**
 * This is the exception class for handling errors for the server.
 */
public class ServerError extends Exception {
    /**
     * This method will return the error code with the appropriate
     * error message with a protocol.
     * @param message - error message
     */
    public ServerError(String message) {
        super(Protocol.ERROR + message);
    }
}
