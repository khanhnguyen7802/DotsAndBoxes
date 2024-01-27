package server;

import java.io.IOException;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;
import networking.SocketConnection;
import protocol.Protocol;


/**
 * This class maintains/encapsulates the connection to the client, handles the input/output streams
 * (because it subclasses SocketConnection),
 * decodes/parses messages FROM THE CLIENT according to the protocol,
 * and encodes/generates messages TO THE CLIENT according to the protocol.
 */
public class ServerConnection extends SocketConnection {
    private ClientHandler clientHandler; // reference to ClientHandler
    protected ServerConnection(Socket socket) throws IOException {
        super(socket);
    }

    /**
     * The setter for the Client handlers.
     * @param clientHandler
     */
    public void setClientHandler(ClientHandler clientHandler) {
        this.clientHandler = clientHandler;
    }

    public enum State{
        IDLE, HELLO, LOGGED_IN, GAME_STARTED
    }

    public State currentState = State.IDLE;

    /**
     * Parse the message from the client.
     * @param msg the message received from the connection
     */
    @Override
    public void handleMessage(String msg) {
        String[] parse = msg.split(Protocol.SEPARATOR);
        String command = parse[0];
        List extras = new ArrayList<>();
        if (parse.length == 2) {
            switch (currentState){
                case IDLE :
                    if (Protocol.HELLO.equals(command)){
                        currentState = State.HELLO;
                        for (int i =2; i < parse.length; i++) {
                            extras.add(parse[i]);
                        }
                        break;
                    }
                case HELLO:
                    if (Protocol.LOGIN.equals(command)){
                        clientHandler.receiveUsername(msg);
                        currentState = State.LOGGED_IN;
                        break;
                    }
                case LOGGED_IN:
                    if (Protocol.NEWGAME.equals(command)){
                        clientHandler.startGame();
                        currentState = State.GAME_STARTED;
                        break;
                    }
                case GAME_STARTED:
                    if (Protocol.MOVE.equals(command)){
                        clientHandler.recieveMove(msg);
                        break;
                    } else {
                        clientHandler.gameOver();
                    }
                default:
                    System.out.println("Incorrect command please try again");
            }
        }
        else {
            System.out.println("Invalid message");
        }
    }
    /**
     * Handle when the server connection is disconnected.
     */
    @Override
    public void handleDisconnect() {
        System.out.println("[SERVER CONNECTION] this is the handler disconnect");
    }

    /**
     * This handles the chat message and sends it.
     * @param msg
     */
    public void send(String msg) {
        super.sendMessage(msg);
    }

    /**
     * Uses the strat method of SocketConnection to start the server connection.
     */
    @Override
    public void start() {
        super.start();
    }
}
