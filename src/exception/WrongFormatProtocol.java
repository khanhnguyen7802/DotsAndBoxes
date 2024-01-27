package exception;

public class WrongFormatProtocol extends Exception {
    // parameterless constructor
    public WrongFormatProtocol() {

    }

    public WrongFormatProtocol(String message) {
        super(message);
    }
}
