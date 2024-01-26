package dotandboxclient;

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


    /**
     * Handle the received messageFromServer from server socket.
     * The protocol can be either HELLO, LOGIN, ALREADYLOGGEDIN, LIST
     * NEWGAME, MOVE, GAMEOVER
     *
     * @param messageFromServer the messageFromServer received from the connection
     */
    @Override
    protected void handleMessage(String messageFromServer) throws WrongFormatProtocol {
        String[] parse = messageFromServer.split(Protocol.SEPARATOR);

        switch(parse[0]) {
            case Protocol.HELLO:
                client.handleHello(messageFromServer);
                break;
            case Protocol.LOGIN:
            case Protocol.ALREADYLOGGEDIN:
                client.handleLogin(messageFromServer);
                break;
            case Protocol.LIST:
                client.handleList(messageFromServer);
                break;
            case Protocol.NEWGAME:
                break;
            case Protocol.MOVE:
                break;
            case Protocol.GAMEOVER:
                break;
            case Protocol.ERROR:
                break;
            default:
                throw new WrongFormatProtocol("The command is in wrong format");
        }
    }

    @Override
    protected void handleDisconnect() {

    }
}
