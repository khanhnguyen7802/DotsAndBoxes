package server;

import game.model.*;
import java.io.IOException;
import java.net.Socket;
import java.util.*;
import networking.SocketServer;
import protocol.Protocol;

/**
 * This class hosts the server for the game Dots and boxes.
 */
public class GameServer extends SocketServer {
    private final List<ClientHandler> clientHandlerList = new ArrayList<>();
    private final List<ClientHandler> inQueue = new ArrayList<>();

    private Integer totalNoOfGames = 0;
    private final Map<ClientHandler, Integer> games = new HashMap<>();

    Map<DotsGame, List<AbstractPlayer>> allGames = new HashMap<>();

    /**
     * Constructs a new ChatServer.
     * @param port the port to listen on
     * @throws IOException if the server socket cannot be created,
     * for example, because the port is already bound.
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
     * This method will block until the server socket is closed,
     * for example by invoking closeServerSocket.
     *
     * @throws IOException if an I/O error occurs when waiting for a connection
     */
    @Override
    public void acceptConnections() throws IOException {
        super.acceptConnections();
    }

    /**
     * Closes the server socket. This will cause the server to stop accepting new connections.
     * If called from a different thread than the one running acceptConnections,
     * then that thread will return from
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
     */
    @Override
    public void handleConnection(Socket socket) {
        System.out.println("A client has connected");
        try {
            var serverConnection = new ServerConnection(
                    socket); // create a connection using a socket
            ClientHandler clientHandler = new ClientHandler(
                    this); // create a handler for the given socket
            clientHandler.setServerConnection(serverConnection);
            serverConnection.setClientHandler(
                    clientHandler); // give reference to client handler for the connection

            addClient(clientHandler);
            serverConnection.start();

        } catch (IOException e) {
            throw new RuntimeException(e);
        }

    }

    /**
     * This adds a client to the Queue.
     * @param client - the current client that has just joined the QUEUE
     */
    public synchronized void addQueue(ClientHandler client) {
        this.inQueue.add(client);
    }


    /**
     * This removes a client from the Queue.
     * @param client - the current client that will be removed from the QUEUE
     */
    public synchronized void removeQueue(ClientHandler client) {
        this.inQueue.remove(client);
    }


    /**
     * This adds a client to the server.
     * @param client - The current client that has just finished the handshake
     */
    public synchronized void addClient(ClientHandler client) {
        this.clientHandlerList.add(client);
        System.out.println("client is added");
    }

    /**
     * A client is removed from the server.
     * @param client - the client that has just disconnected
     */
    public synchronized void removeClient(ClientHandler client) {
        this.clientHandlerList.remove(client);
        System.out.println("client is removed");
        if (inQueue.contains(client)) {
            ArrayList<String> users = new ArrayList<>();
            // finish game if a player loses connection
            removeQueue(client);
            if (getGameId(client) != -1) {
                for (Map.Entry<ClientHandler, Integer> current : games.entrySet()) {
                    // iterate through all games and find the players, having their names as
                    //the unique identifier
                    if (current.getValue() == getGameId(client)) {
                        current.getKey().gameOver(
                                Protocol.DISCONNECT + Protocol.SEPARATOR + current.getKey()
                                        .getUsername());
                        users.add(current.getKey().getUsername());
                        removeQueue(current.getKey());
                        DotsGame ownGame = currentGame(users);
                        allGames.remove(ownGame);

                    }
                }
            }
        }
    }

    /**
     * This method receives the Username and checks if there
     * is a Username with the same name.
     * @param name - username of the client.
     * @return true || false
     */
    public boolean handleUsername(String name) {
        for (ClientHandler handler : clientHandlerList) {
            if (name.equals(handler.getUsername())) {
                return true;
            }
        }
        return false;
    }

    /**
     * This method will create the list of all client names.
     * That are logged in.
     * @param requester - the client requesting the list
     */
    public void handleList(ClientHandler requester) {
        String list = Protocol.LIST;
        for (ClientHandler handler : clientHandlerList) {
            if (handler.getUsername() != null) {
                list = list.concat(Protocol.SEPARATOR + handler.getUsername());
            }
        }
        requester.listPrinter(list);
    }

    /**
     * This method will receive the client that requests QUEUE, and will add it to a new game
     * if there are enough clients to play a game.
     * @param handlers - client requesting to join the queue
     */
    public synchronized void handleQueue(ClientHandler handlers) {
        addQueue(handlers); // add handlers to be in the queue
        List<String> user = new ArrayList<>();
        List<ClientHandler> inHandler = new ArrayList<>();
        int counter = 0;
        if (inQueue.size() > 1 && inQueue.size() % 2 == 0) {
            // if there are enough players create
            //a game
            for (ClientHandler handler : inQueue) { //iterate through only the players in queue
                user.add(handler.getUsername());
                inHandler.add(handler);
                counter++;
                if (counter == 2) {
                    for (int i = 0; i < 2; i++) {
                        inHandler.get(i).startGame(user.get(0), user.get(1));
                        games.put(inHandler.get(i), totalNoOfGames);
                        createGame(user.get(0), user.get(1));
                        //create a game with the current players, having the index of the total no
                        // of games ever started
                    }
                    totalNoOfGames++; // number of games +1
                    break;
                }
            }
        }
    }

    /**
     * This method will create the game for two players.
     * @param pl1 - first player
     * @param pl2 - second player
     */
    public void createGame(String pl1, String pl2) {
        AbstractPlayer player1 = new HumanPlayer(pl1, Mark.AA);
        AbstractPlayer player2 = new HumanPlayer(pl2, Mark.BB);
        // create the player objects for a game of Dots and Boxes
        List<AbstractPlayer> currentPlayers = new ArrayList<>();
        currentPlayers.add(player1);
        currentPlayers.add(player2);
        DotsGame dotGame = new DotsGame(player1, player2); // create the game for the players
        allGames.put(dotGame, currentPlayers); // add the game to the list of all games
    }

    public int getGameId(ClientHandler user) {
        for (Map.Entry<ClientHandler, Integer> current : games.entrySet()) {
            // iterate through all games and find the players, having their names as
            //the unique identifier
            if (Objects.equals(current.getKey(), user)) {
                return current.getValue();
            }
        }
        return -1;
    }

    /**
     * This method checks if players are in a game together. And checks
     * where is their game stored in the list of all games
     * @param users -
     * @return players in a game together.
     */
    public DotsGame currentGame(ArrayList<String> users) {
        for (Map.Entry<DotsGame, List<AbstractPlayer>> dotsGame : allGames.entrySet()) {
            // iterate through all games and find the players, having their names as
            //the unique identifier
            try {
                if (Objects.equals(dotsGame.getValue().get(0).getName(),
                                   users.get(0)) || Objects.equals(
                        dotsGame.getValue().get(0).getName(), users.get(1))) {
                    return dotsGame.getKey();
                }
            } catch (IndexOutOfBoundsException g) {
                System.out.println(Protocol.ERROR + Protocol.SEPARATOR + Protocol.DISCONNECT);
            }
        }
        return null;
    }

    /**
     * This method will initiate the game, and selects the players that are in
     * a game together. And afterward it will receive the moves, checks for the
     * validity of the move, if valid it will send the move to all players
     * in the current game.
     * @param msg - the move
     * @param current - the current player doing the move
     */
    public synchronized void allIngame(String msg, ClientHandler current) {
        int no = games.get(current);
        List<ClientHandler> handlers = new ArrayList<>();
        ArrayList<String> users = new ArrayList<>();
        for (Map.Entry<ClientHandler, Integer> entry : games.entrySet()) {
            // searches through all games to find the current game
            // by the players usernames.
            if (entry.getValue() == no) {
                handlers.add(entry.getKey());
                users.add(entry.getKey().getUsername());
                if (handlers.size() == 2) {
                    break; // Stop after finding two keys
                }
            }
        }
        if (users.size() == 2) {
            DotsGame dotsGame = currentGame(users);
            // create a temporary game obj from the stored game
            for (ClientHandler handler : handlers) {
                String[] tokens = msg.split(Protocol.SEPARATOR);
                int integer = Integer.parseInt(tokens[1]);
                HumanPlayer currentPlayer = (HumanPlayer) dotsGame.getTurn(); // current player
                Move determinedMove = new DotsMove(dotsGame.getBoard().toRow(integer),
                                                   dotsGame.getBoard().toColumn(integer),
                                                   currentPlayer.getMark());
                dotsGame.doMove(determinedMove);
                handler.move(msg); // make the move of the player
                if (dotsGame.isGameover()) {
                    removeQueue(handler);
                }
                if (dotsGame.isGameover() || games.size() <= 1) {
                    if (dotsGame.getBoard().hasWinner() && dotsGame.isGameover()) {
                        // finish game if there is a winner
                        handler.gameOver(Protocol.VICTORY + Protocol.SEPARATOR + dotsGame.getWinner());
                    }
                    if (dotsGame.isGameover() && !dotsGame.getBoard().hasWinner()) {
                        // finish game if it ends in a draw
                        handler.gameOver(Protocol.DRAW);

                    }
                    allGames.remove(dotsGame);

                }
            }
        } else {
            current.gameOver(Protocol.VICTORY + Protocol.SEPARATOR + current.getUsername());
        }

    }


    /**
     * This is the main runnable method.
     * @param args - arguments of the main method
     * @throws IOException - Signals that an I/O exception, of some sort has occurred.
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
            } catch (IOException e) {
                System.out.println("The server has been disconnected");
            }
        }


        if (portNumber == 0) { // connect to a random port if we type in 0
            portNumber = server.getPort();

        }
        System.out.println("Port " + portNumber + " is used");

        server.acceptConnections();
    }

}
