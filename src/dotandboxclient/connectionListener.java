package dotandboxclient;

/**
 * Keep logs of the chat by writing all received messages to a file.
 */
public class connectionListener implements ClientListener {

    /**
     * Constructor for LogListener class.
     * @param logFileName the name of the output log file
     */
    public connectionListener(String logFileName) {
    }

    @Override
    public void printMenu() {

    }

    /**
     * Method dealing with lost connection.
     */
    @Override
    public void connectionLost() {
        System.out.println("[LogListener]: Connection Lost");
    }


}

