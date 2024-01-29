package exception;

/**
 * This is the written exception.
 * It is used to throw when the Protocol is in invalid syntax.
 */
public class WrongFormatProtocol extends Exception {
    // parameterless constructor
    public WrongFormatProtocol() {

    }

    public WrongFormatProtocol(String message) {
        super(message);
    }
}
