package dotandboxclient;
import exception.WrongFormatProtocol;
import java.io.IOException;
import java.net.InetAddress;
import java.util.ArrayList;
import java.util.List;
import networking.*;
import protocol.Protocol;

public class DotAndBoxClient {
    public static final String gameName = "Resit-8 game";
    private ClientConnection clientConnection;
    private String usernameLoggedIn;
    private boolean isLoggedIn;
    private boolean isConnectedToServer;
    private boolean isQueued;

//    private List<ClientListener> listeners;

    /**
     * This is the constructor for the Client.
     * @param address the address to connect to
     * @param port the port to connect to
     * @throws IOException
     */
    DotAndBoxClient(InetAddress address, int port) throws IOException {
        this.clientConnection = new ClientConnection(address, port, this);
        this.isConnectedToServer = true;

        this.usernameLoggedIn = null;
        this.isLoggedIn = false;
        this.isQueued = false;
//        this.listeners = new ArrayList<>();
    }

    /**
     * Close the connection by calling the handleDisconnect method of the
     * Client connection.
     */
    void close() {
        clientConnection.handleDisconnect();
    }


    /**
     * Send HELLO command to the server socket
     * by delegating to the clientConnection to do its job.
     */
    public void sendHello() {
        this.clientConnection.sendHello();
    }

    /**
     * Handle HELLO command from the server,
     * which is HELLO~<server description>.
     */
    public void handleHello(String receivedMsg) throws WrongFormatProtocol {
        if (receivedMsg.split(Protocol.SEPARATOR).length < 2)
            throw new WrongFormatProtocol("The command is in wrong format");
        else {
            clientTUI.printMenu();
            clientTUI.printToConsole("In order to start game, you need LOGIN first!");
        }
    }

    /**
     * Send LOGIN command to the server socket
     * by delegating to the clientConnection to do its job.
     */
    public void sendLogin(String username) {
        if (isLoggedIn) { // if the client has already logged in
            System.out.println("You have already logged in");
        } else {
            this.usernameLoggedIn = username;

            this.clientConnection.sendLogin(username);
        }
    }

    /**
     * Handle LOGIN command from the server,
     * which is LOGIN.
     */
    public void handleLogin(String receivedMessage) {
        if (receivedMessage.equals(Protocol.LOGIN)) { // if the user is not logged in yet
            System.out.println("Logged in as " + this.usernameLoggedIn);
            this.isLoggedIn = true;
        } else {
            clientTUI.printToConsole("You're already logged in / This name has been taken");
            clientTUI.printToConsole("Please choose another option / name");
        }
    }

    public void sendList() {
        clientConnection.sendList();
    }

    public void handleList(String receivedMessage) {
        String[] activePlayers = receivedMessage.split("~");
        System.out.print("Active players:");

        for (String activePlayer : activePlayers)
            System.out.print(" " + activePlayer);
    }

    /**
     * Send QUEUE command to the server socket
     * by delegating to the clientConnection to do its job.
     */
    public void sendQueue() {
        if (isQueued == true) {
            System.out.println("The client is already in a queue!");
        } else {
            clientConnection.sendQueue();
        }
    }

    public void handleNewGame() {

    }

    public void sendMove() {

    }


    /**
     * Adds a listener to the client (a listener is considered a receiver).
     * @param listener the particular Listener
     */
    public void addListener(ClientListener listener){
        listeners.add(listener);
    }

    /**
     * Removes a listener from the client.
     * @param listener the particular Listener
     */
    void removeListener(ClientListener listener){
        listeners.remove(listener);
    }

}
