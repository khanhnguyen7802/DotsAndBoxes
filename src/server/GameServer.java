package server;

import game.model.*;
import java.io.IOException;
import java.net.Socket;
import java.util.*;
import networking.SocketServer;
import protocol.Protocol;

public class GameServer extends SocketServer {
    List<ClientHandler> clientHandlerList = new ArrayList<>();
    List<ClientHandler> inQueue = new ArrayList<>();

    Set<Set<ClientHandler>> games = new HashSet<Set<ClientHandler>>();

    private DotsGame dotsGame;
    private DotsMove move;
    private AbstractPlayer player1;
    private AbstractPlayer player2;


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


    public synchronized void addQueue(ClientHandler client) {
        this.inQueue.add(client);
    }


    public synchronized void removeQueue(ClientHandler client) {
        this.inQueue.remove(client);
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

    public synchronized void handleQueue(ClientHandler handlers) throws IOException {
        inQueue.add(handlers);
        List<String> user = new ArrayList<>();
        List<ClientHandler> inHandler = new ArrayList<>();
        Set<ClientHandler> inGame= new HashSet<ClientHandler>();
        int counter=0;
        if (inQueue.size() >1 && inQueue.size() % 2 == 0){
        for(ClientHandler handler : inQueue) {
            user.add(handler.getUsername());
            inHandler.add(handler);
            counter++;
            if(counter == 2){
                for (int i = 0; i < 2; i++ ) {
                    inHandler.get(i).startGame(user.get(0), user.get(1));
                    removeQueue(inHandler.get(i));
                    inGame.add(inHandler.get(i));
                    games.add(inGame);
                }
                player1 = new HumanPlayer(user.get(0), Mark.AA);
                player2 = new HumanPlayer(user.get(1), Mark.BB);
                dotsGame = new DotsGame(player1, player2);
                counter = 0;
                user = new ArrayList<>();
                inHandler = new ArrayList<ClientHandler>();
                inGame = new HashSet<ClientHandler>();
                break;
            }
            }
        }
    }

    public synchronized void allIngame(String msg){
        String[] tokens = msg.split(Protocol.SEPARATOR);
        Integer move = Integer.parseInt(tokens[1]);
        HumanPlayer currentPlayer = (HumanPlayer) dotsGame.getTurn(); // current player
        Move determinedMove = new DotsMove(dotsGame.getBoard().toRow(move),
                                           dotsGame.getBoard().toColumn(move),
                                           currentPlayer.getMark()); // get the move
        dotsGame.doMove(determinedMove);
        for(Set<ClientHandler> handlers : games) {
            for (ClientHandler handler : handlers) {
                if (handlers.size() > 1 && !dotsGame.isGameover()){
                    handler.move(msg);
                if (dotsGame.getBoard().hasWinner()) {
                    handler.gameOver(Protocol.VICTORY + Protocol.SEPARATOR + dotsGame.getWinner());
                }
                if (dotsGame.isGameover() && !dotsGame.getBoard().hasWinner()){
                    handler.gameOver(Protocol.DRAW);
                }

            }else {
                    handler.gameOver(Protocol.DISCONNECT + Protocol.SEPARATOR + handler.getUsername());
            }
            }
            break;
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