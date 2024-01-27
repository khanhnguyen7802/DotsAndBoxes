package dotandboxclient;

import exception.WrongFormatProtocol;
import java.io.IOException;
import java.net.InetAddress;
import networking.SocketConnection;
import protocol.Protocol;

public class ClientConnection extends SocketConnection {
    private DotAndBoxClient client;

    /**
     * The constructor fot the CLientConnection.
     * As soon as a ClientConnection is created, it invokes start() method
     * to start a thread reading messages.
     *
     * @param host the address of the host
     * @param port the port that server is at
     * @param client the particular client
     * @throws IOException
     */
    protected ClientConnection(InetAddress host, int port, DotAndBoxClient client) throws IOException {
        super(host, port);
        this.client = client;
        start();
    }

    @Override
    public void handleStart() {
        System.out.println("[CLIENT_CONNECTION] Start reading from the socket");
    }
    /**
     * Handle the received messageFromServer from server socket.
     * The protocol can be either HELLO, LOGIN, ALREADYLOGGEDIN, LIST
     * NEWGAME, MOVE, GAMEOVER
     *
     * @param messageFromServer the messageFromServer received from the connection
     */
    @Override
    public void handleMessage(String messageFromServer) throws WrongFormatProtocol {
        String[] parse = messageFromServer.split(Protocol.SEPARATOR);

        switch (parse[0]) {
            case Protocol.HELLO:
                System.out.println(messageFromServer);

                try {
                    client.handleHello(messageFromServer);
                } catch (WrongFormatProtocol e) {
                    System.out.println("[CLIENT_CONNECTION] Invalid protocol");
                }
                break;
            case Protocol.LOGIN:
            case Protocol.ALREADYLOGGEDIN:
                client.handleLogin(messageFromServer);
                break;
            case Protocol.LIST:
                client.handleList(messageFromServer);
                break;
            case Protocol.NEWGAME:
                client.handleNewGame(messageFromServer);
                break;
            case Protocol.MOVE:
                client.handleMove(messageFromServer);
                break;
//            case Protocol.GAMEOVER:
//                client.handleGameOver();
//                break;
//            case Protocol.ERROR:
//                break;
            default:
                throw new WrongFormatProtocol("The command is in wrong format");
        }
    }

    @Override
    protected void handleDisconnect() {
    }

    /**
     * Send HELLO command to the server.
     */
    public void sendHello() {
        sendMessage(Protocol.HELLO + Protocol.SEPARATOR + DotAndBoxClient.gameName);
    }

    /**
     * Send LOGIN command to the server.
     */
    public void sendLogin(String username) {
        sendMessage(Protocol.LOGIN + Protocol.SEPARATOR + username);
    }

    /**
     * Send LIST command to the server.
     */
    public void sendList() {
        sendMessage(Protocol.LIST);
    }

    public void sendQueue() {
        sendMessage(Protocol.QUEUE);
    }

    public void sendMove(int idx) {
        sendMessage(Protocol.MOVE + Protocol.SEPARATOR + idx);
    }


}
