package server;

import java.io.IOException;
import protocol.Protocol;

/**
 * This class handles the client and its interactions with the server.
 */
public class ClientHandler {
    private ServerConnection serverConnection;
    private final GameServer gameServer;
    private String username;

    /**
     * Constructor to create a new ClientHandler.
     * @param server the chat server that this client handler refers to
     */
    public ClientHandler(GameServer server) throws IOException {
        this.gameServer = server;
        this.username = null;
    }

    /**
     * Set the server connection for this client handler.
     * @param serverConnection the server connection that this client refers to
     */
    public void setServerConnection(ServerConnection serverConnection) {
        this.serverConnection = serverConnection;
    }

    /**
     * Get the username of the client handler.
     * @return the username of the client
     */
    public String getUsername() {
        return this.username;
    }

    /**
     * Receive and set the name of the user when the user first logs in.
     * @param msg the protocol that clients send to server (LOGIN~<msg>)
     */
    public void receiveUsername(String msg) {
        String[] tokens = msg.split(Protocol.SEPARATOR);
        String name = tokens[1];
        if (gameServer.handleUsername(name)) {
            alreadyLoggedIn();
        } else {
            if (username == null) { // LOGIN~<msg>
                username = name;
            }
        }

    }

    /**
     * This method receives the request for joining a QUEUE.
     */
    public void receiveQueue() {
        gameServer.handleQueue(this);
    }

    /**
     * Removes a player from the Queue.
     */
    public void disconnectQueue() {
        gameServer.removeQueue(this);
    }

    /**
     *
     */
    public void handShake() {
        if (serverConnection.currentState == ServerConnection.State.I) {
            serverConnection.send(Protocol.HELLO + Protocol.SEPARATOR + "Server of resit-8");
        } else if (serverConnection.currentState == ServerConnection.State.H) {
            //this is the case when the player enters a username that has already been entered
            serverConnection.send(Protocol.ALREADYLOGGEDIN);
        } else {
            serverConnection.send(Protocol.LOGIN);
        }
    }

    /**
     * This method receives the request for printing out a list.
     */
    public void listClients() {
        this.gameServer.handleList(this);
    }

    /**
     * This method will list all players connected to the server.
     * @param msg - List of all players with the protocol
     */
    public void listPrinter(String msg) {
        serverConnection.send(msg);
    }

    /**
     * If the client is disconnected, that client should be removed.
     */
    public void handleDisconnect() {
        System.out.println("[CLIENT_HANDLER] Disconnected");
        this.gameServer.removeClient(this);
    }


    /**
     * This method will initiate a game for a player and
     * sets who are the first and second player.
     * @param player1 - the first player in the game.
     * @param player2 - the second player in the game.
     */
    public void startGame(String player1, String player2) {
        serverConnection.send(
                Protocol.NEWGAME + Protocol.SEPARATOR + player1 + Protocol.SEPARATOR + player2);
    }

    /**
     * This method receives the move from the client
     * that can do a move.
     * @param msg - the move
     */
    public void receiveMove(String msg) {
        this.gameServer.allIngame(msg, this);

    }

    /**
     * This method send the move done to all clients
     * in a game.
     * @param msg - the move.
     */
    public void move(String msg) {
        serverConnection.send(msg);
    }

    /**
     * This method is called when a game is over.
     * @param msg - the reason for ending the game
     */
    public synchronized void gameOver(String msg) {
        serverConnection.send(Protocol.GAMEOVER + Protocol.SEPARATOR + msg);
        serverConnection.currentState = ServerConnection.State.L;
    }

    /**
     * This method checks sets the state back to non Logged in.
     */
    // @
    public void alreadyLoggedIn() {
        serverConnection.currentState = ServerConnection.State.H;
    }
}
