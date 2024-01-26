package server;

import java.io.IOException;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;
import networking.SocketServer;

public class GameServer extends SocketServer {
    List<ClientHandler> clientHandlerList = new ArrayList<>();


    /**
     * Constructs a new ChatServer.
     * @param port the port to listen on
     * @throws IOException if the server socket cannot be created, for example, because the port is already bound.
     */
    public GameServer(int port) throws IOException {
        super(port);
    }

    /**
     * Returns the port on which this server is listening for connections.
     *
     * @return the port on which this server is listening for connections
     */
    @Override
    public int getPort() {
        return super.getPort();
    }

    /**
     * Accepts connections and starts a new thread for each connection.
     * This method will block until the server socket is closed, for example by invoking closeServerSocket.
     *
     * @throws IOException if an I/O error occurs when waiting for a connection
     */
    @Override
    public void acceptConnections() throws IOException {
        super.acceptConnections();
    }

    /**
     * Closes the server socket. This will cause the server to stop accepting new connections.
     * If called from a different thread than the one running acceptConnections, then that thread will return from
     * acceptConnections.
     */
    @Override
    public synchronized void close() {
        System.out.println("The server is disconnected!");
        super.close();

    }

    /**
     * Creates a new connection handler for the given socket.
     *
     * @param socket the socket for the connection
     * @return the connection handler
     */
    @Override
    public void handleConnection(Socket socket) {
        System.out.println("A client has connected");
        try {
            var serverConnection = new ServerConnection(socket); // create a connection using a socket
            ClientHandler clientHandler = new ClientHandler(this); // create a handler for the given socket
            clientHandler.setServerConnection(serverConnection);
            serverConnection.setClientHandler(clientHandler); // give reference to client handler for the connection

            addClient(clientHandler);
            serverConnection.start();

        } catch (IOException e) {
            throw new RuntimeException(e);
        }

    }

    /**
     * This adds a client to the server.
     * @param client
     */
    public synchronized void addClient(ClientHandler client) {
        this.clientHandlerList.add(client);
        System.out.println("client is added");
    }

    /**
     * A client is removed from the server.
     * @param client
     */
    public synchronized void removeClient(ClientHandler client) {
        this.clientHandlerList.remove(client);
        System.out.println("client is removed");
    }


    /**
     * Handle  a chat message that is received (by a client that already has a username).
     * @param from - the client that sends the msg
     * @param msgContent - content of the msg
     */
    public void handleMove(String msgContent) {
        for(ClientHandler handler : clientHandlerList) {
            handler.recieveMove(msgContent);
        }
    }

    /**
     * This is the main runnable method.
     * @param args
     * @throws IOException
     */
    public static void main(String[] args) throws IOException {
        GameServer server;
        Scanner sc = new Scanner(System.in);
        int portNumber;
        while (true) {
            try {
                String line;
                System.out.print("Enter a port number: ");
                line = sc.nextLine();
                portNumber = Integer.parseInt(line);
                server = new GameServer(portNumber);
                break;
            } catch (NumberFormatException e) {
                System.out.println("Port number should be a number");
            } catch (IllegalArgumentException e) {
                System.out.println("The port must be a positive number");
            }
        }



        if(portNumber == 0) {
            portNumber = server.getPort();
            System.out.println("Port " + portNumber + " is used");
        }

        server.acceptConnections();
    }

}
