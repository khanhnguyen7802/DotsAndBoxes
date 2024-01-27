package server;

import java.io.IOException;
import protocol.Protocol;

public class ClientHandler {
    private ServerConnection serverConnection;
    private GameServer gameServer;
    private String username;

    /**
     * Constructor to create a new ClientHandler.
     * @param server the chat server that this client handler refers to
     * @throws IOException
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
        if (username==null) { // LOGIN~<msg>
            String[] tokens = msg.split(Protocol.SEPARATOR);
            String name = tokens[1];
            username = name;
        } else {
            alreadyLoggedIn();
        }

    }

    public void recieveQueue() throws IOException {
        gameServer.handleQueue(this);
    }

    public void disconnectQueue() throws IOException {
        gameServer.removeQueue(this);
    }

    public void handShake(){
        if (serverConnection.currentState == ServerConnection.State.IDLE){
        serverConnection.send(Protocol.HELLO+Protocol.SEPARATOR);}
        else {
            serverConnection.send(Protocol.LOGIN);
        }
    }

    public void errorHandling(String msg){
        serverConnection.send(Protocol.ERROR+Protocol.SEPARATOR+msg);
    }


    public void receiveMessage(String msg){
        if (username!=null) { // SAY~<msg>
            String[] parse = msg.split(Protocol.SEPARATOR);
            String msgContent = parse[1];

            gameServer.handleMove(msgContent);

        } else {
            System.out.println("ignored: user must log in first");
        }
    }

    /**
     * If the client is disconnected, that client should be removed.
     */
    public void handleDisconnect() {
        System.out.println("[CLIENT_HANDLER] Disconnected");
        this.gameServer.removeClient(this);
    }


    public void startGame(String player1, String player2) {
        serverConnection.send(Protocol.NEWGAME+Protocol.SEPARATOR+player1+Protocol.SEPARATOR+ player2);
    }

    public void recieveMove(String msg) {
        this.gameServer.allIngame(msg);

    }
    public void move(String msg){
        serverConnection.send(msg);
    }

    public void gameOver(String msg){
        serverConnection.send(Protocol.GAMEOVER+Protocol.SEPARATOR+msg);
        serverConnection.currentState = ServerConnection.State.LOGGED_IN;
    }

    public void alreadyLoggedIn(){
        serverConnection.send(Protocol.ALREADYLOGGEDIN);
        serverConnection.currentState = ServerConnection.State.HELLO;
    }
}
