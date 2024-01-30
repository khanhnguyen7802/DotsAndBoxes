package server;

import exception.ServerError;
import java.io.IOException;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Arrays;
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
    public State currentState;

    /**
     * Constructor for ServerConnection.
     *
     * @param socket The socket to establish the connection.
     * @throws IOException - If an I/O error occurs.
     */
    protected ServerConnection(Socket socket) throws IOException {
        super(socket);
        currentState = State.I;
    }

    /**
     * The setter for the Client handlers.
     * @param clientHandler - the client handler
     */
    public void setClientHandler(ClientHandler clientHandler) {
        this.clientHandler = clientHandler;
    }

    /**
     * This class defines States.
     * These are the States of a client.
     * I : IDLE
     * H : HELLO
     * L : Logged in
     * G : in game
     * We have these states so that the clients cannot do illegal commands
     * when they were not meant to do them.
     */
    public enum State {
        I, H, L, G
    }

    /**
     * Parse the message from the client.
     * @param msg the message received from the connection
     */
    @Override
    public void handleMessage(String msg) throws IOException, ServerError {
        String[] parse = msg.split(Protocol.SEPARATOR);
        String command = parse[0];
        switch (currentState) {
            case I:
                if (Protocol.HELLO.equals(command)) {
                    clientHandler.handShake();
                    currentState = State.H;
                    // we do not have any extras implemented
                    List<String> extras = new ArrayList<>(
                            Arrays.asList(parse).subList(2, parse.length));
                    break;
                } else {
                    throw new ServerError("HELLO expected");
                }
            case H:
                if (Protocol.LOGIN.equals(command)) {
                    currentState = State.L;
                    clientHandler.receiveUsername(msg); // check for the username conditions
                    clientHandler.handShake(); // finish handshake
                    break;
                } else {
                    throw new ServerError("LOGIN expected");
                }
            case L:
                if (Protocol.QUEUE.equals(command)) {
                    clientHandler.receiveQueue(); // add/remove player from the queue
                    currentState = State.G;
                    break;
                } else if (Protocol.LIST.equals(command)) {
                    clientHandler.listClients();
                    break;
                } else {
                    throw new ServerError("QUEUE expected");
                }
            case G:
                if (Protocol.MOVE.equals(command)) {
                    clientHandler.receiveMove(msg);
                    break;
                } else if (Protocol.QUEUE.equals(command)) {
                    clientHandler.disconnectQueue(); // remove player from the game
                } else if (Protocol.LIST.equals(command)) {
                    clientHandler.listClients();
                    break;
                } else {
                    throw new ServerError("Incorrect MOVE expected");
                }
                break;
            default:
                throw new ServerError("incorrect command please try again");
        }
    }

    /**
     * Handle when the server connection is disconnected.
     */
    @Override
    public void handleDisconnect() {
        System.out.println("[SERVER CONNECTION] this is the handler disconnect");
        clientHandler.handleDisconnect();
    }

    /**
     * This handles the chat message and sends it.
     * @param msg - message
     */
    public void send(String msg) {
        super.sendMessage(msg);
    }

    /**
     * Uses the start method of SocketConnection to start the server connection.
     */
    @Override
    public void start() {
        super.start();
    }
}
