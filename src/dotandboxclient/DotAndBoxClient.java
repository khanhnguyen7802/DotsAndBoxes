package dotandboxclient;

import exception.WrongFormatProtocol;
import game.TUI.AiTUI;
import game.ai.ComputerPlayer;
import game.ai.NaiveStrategy;
import game.ai.SmartStrategy;
import game.ai.Strategy;
import game.model.*;
import java.io.IOException;
import java.net.InetAddress;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;
import protocol.Protocol;

public class DotAndBoxClient {
    public static final String gameName = "Resit-8 game";
    //@ private invariant clientConnection != null;
    //@ private invariant isLoggedIn == false || isLoggedIn == true;
    //@ private invariant isQueued == false || isQueued == true;
    //@ private invariant isInGame == false || isInGame == true;

    private ClientConnection clientConnection;
    private DotAndBoxClientTUI dotAndBoxClientTUI;
    private AiTUI aiTUI;
    private String usernameLoggedIn;
    private AbstractPlayer currentPlayer;
    private DotsGame game;
    private ClientState currentState;
    private boolean isBot = false;
    private boolean isBotTurn;
    private boolean isSmart = false;
    private boolean isLoggedIn;
    private boolean isConnectedToServer;
    private boolean isQueued;
    private boolean isInGame;
    private List<ClientListener> listeners;
    public enum ClientState {
        IDLE, LOGGED_IN, IN_QUEUE,IN_GAME
    }

    public void setCurrentState(ClientState state) {
        this.currentState = state;
    }

    public ClientState getCurrentState() {
        return this.currentState;
    }

    /**
     * This is the constructor for the Client.
     * @param address the address to connect to
     * @param port the port to connect to
     * @throws IOException
     */
    public DotAndBoxClient(InetAddress address, int port) throws IOException {
        this.clientConnection = new ClientConnection(address, port, this);
        this.isConnectedToServer = true;
        this.dotAndBoxClientTUI = new DotAndBoxClientTUI();
        this.listeners = new ArrayList<>();
        this.aiTUI = new AiTUI();


        this.usernameLoggedIn = null;
        this.isLoggedIn = false;
        this.isQueued = false;
        this.isInGame = false;
    }

    public boolean chooseBot() {
        return isBot;
    }

    public boolean isBotTurn() {
        return isBotTurn;
    }

    /**
     * Close the connection by calling the handleDisconnect method of the
     * Client connection.
     */
    void close() {
        clientConnection.handleDisconnect();
    }
    public void handleDisconnect() {
        System.out.println("[CLIENT]: Disconnected");
        for (ClientListener listener : listeners) {
            listener.connectionLost();
        }
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

    /**
     * Send HELLO command to the server socket
     * by delegating to the clientConnection to do its job.
     *
     * ClientConnection will use the sendMessage() method to
     * send the command HELLO to the server socket.
     */
    //@pure;
    public void sendHello() {
        this.clientConnection.sendHello();
    }

    /**
     * Handle HELLO command from the server,
     * which is HELLO~<server description>.
     *
     * Then print out the help menu and ask the user to perform LOGIN operation.
     */
    public void handleHello(String receivedMsg) throws WrongFormatProtocol {
        System.out.println("[CLIENT] Handle hello");
        if (receivedMsg.split(Protocol.SEPARATOR).length < 2) {
            throw new WrongFormatProtocol("The command is in wrong format");
        } else {
            dotAndBoxClientTUI.printMenu();
            System.out.println("In order to start game, you need LOGIN first!");

        }
    }

    /**
     * Send LOGIN command to the server socket
     * by delegating to the clientConnection to do its job.
     *
     * ClientConnection will use the sendMessage() method to
     * send the command LOGIN to the server socket.
     */
    //@pure;
    public void sendLogin(String username) {
        if (isLoggedIn) { // if the client has already logged in
            System.out.println("You have already logged in");
        } else {
            if (username.equals("")) {
                System.out.print("What is your username? ");
                Scanner scanner = new Scanner(System.in);
                this.usernameLoggedIn = scanner.nextLine();
                this.clientConnection.sendLogin(this.usernameLoggedIn);

            } else {
                this.usernameLoggedIn = username;

                this.clientConnection.sendLogin(username);
            }
        }
    }

    /**
     * Handle LOGIN command from the server,
     * which is LOGIN.
     *
     * If the user is already logged in (i.e., same name is used to log in),
     * then ask the user to choose another option (or name).
     */
    public void handleLogin(String receivedMessage) {
        if (receivedMessage.equals(Protocol.LOGIN)) { // if the user is not logged in yet
            System.out.println("Logged in as " + this.usernameLoggedIn);
            this.isLoggedIn = true;
        } else {
            System.out.println("You're already logged in / This name has been taken");
            System.out.println("Please choose another option / name");

            dotAndBoxClientTUI.handleInputCommands();
        }
    }

    /**
     * Send LIST command to the server socket
     * by delegating to the clientConnection to do its job.
     *
     * ClientConnection will use the sendMessage() method to
     * send the command LIST to the server socket.
     */
    //@pure;
    public void sendList() {
        if (isLoggedIn) {
            clientConnection.sendList();
        } else { System.out.println("You're not logged in yet."); }
    }

    /**
     * Handle LIST command from the server,
     * which is LIST.
     *
     * Show all the users that are currently logged into the server.
     */
    //@pure;
    public void handleList(String receivedMessage) {
        System.out.println(receivedMessage);
        String[] activePlayers = receivedMessage.split("~");
        System.out.print("Active players:");

        for (int i = 1; i < activePlayers.length; i++) {
            System.out.print(" " + activePlayers[i]);
        }
        System.out.println("");

        //        dotAndBoxClientTUI.handleInputCommands();
    }

    /**
     * Send QUEUE command to the server socket
     * by delegating to the clientConnection to do its job.
     *
     * ClientConnection will use the sendMessage() method to
     * send the command QUEUE to the server socket.
     */
    //@pure;
    public void sendQueue() {
        if (isLoggedIn) {
            if (isQueued && !isInGame) { // in queue but not in game
                System.out.println("You're already in a queue! Are you sure you want to leave (Y/N)?");
                Scanner scanner = new Scanner(System.in);
                String answer = scanner.nextLine();

                if (answer.toUpperCase().equals("Y")) {
                    clientConnection.sendQueue();
                    isQueued = false;
                    System.out.println("Successfully left the queue !!!");
                    this.currentState = ClientState.LOGGED_IN;
                }

            } else if (isQueued && isInGame) {
                System.out.println("Cannot queue because you're in a game");
            } else { // join the queue
                isQueued = true;
                this.currentState = ClientState.IN_QUEUE;

                Scanner scanner = new Scanner(System.in);
                String typeOfPlayer;
                String typeOfAI;

                // Choose AI or not?
                System.out.println("Do you want AI to play for you? (y/n):");
                typeOfPlayer = scanner.nextLine();

                while (!typeOfPlayer.equalsIgnoreCase("y") && !typeOfPlayer.equalsIgnoreCase("n")) {
                    System.out.println("Please enter your option again (y/n):");
                    typeOfPlayer = scanner.nextLine();
                }

                // if AI is chosen
                if (typeOfPlayer.equalsIgnoreCase("y")) {
                    isBot = true;
                    // Ask which AI
                    System.out.print("What type (naive/smart) of AI do you want to use (-n/-s)?: ");
                    typeOfAI = scanner.nextLine();

                    while (!typeOfAI.equalsIgnoreCase("-n") && !typeOfAI.equalsIgnoreCase("-s")) {
                        System.out.print("Please enter your option again (-n/-s): ");
                        typeOfAI = scanner.nextLine();
                    }

                    // if this is indeed our turn
                    // then create a corresponding player
                    if (typeOfAI.equalsIgnoreCase("-s")) {
                        isSmart = true;
                    }
                }

                System.out.println("Successfully joined the queue !!!");

                clientConnection.sendQueue();

//                while(isQueued) {
//                    System.out.println("1");
//                    try {
//                        Thread.sleep(500);
//                    } catch (InterruptedException e) {
//                        throw new RuntimeException(e);
//                    }
//                }
            }


        } else {
            System.out.println("You're not logged in yet.");
        }
    }

    /**
     * Send QUEUE command to the server socket
     * by delegating to the clientConnection to do its job.
     *
     * ClientConnection will use the sendMessage() method to
     * send the command QUEUE to the server socket.
     */
    //@pure;
    public void sendQueueAI() {
        if (isLoggedIn) {
            if (isQueued && !isInGame) { // in queue but not in game
                System.out.println("You're already in a queue! Are you sure you want to leave (Y/N)?");
                Scanner scanner = new Scanner(System.in);
                String answer = scanner.nextLine();

                if (answer.toUpperCase().equals("Y")) {
                    clientConnection.sendQueue();
                    System.out.println("Successfully left the queue !!!");
                    isQueued = false;
                }

            } else if (isQueued && isInGame) {
                System.out.println("Cannot queue because you're in a game");
            } else { // join the queue
                isBot = true;
                // Ask which AI
                System.out.print("What type (naive/smart) of AI do you want to use (-n/-s)?: ");
                Scanner scanner = new Scanner(System.in);
                String typeOfAI;
                typeOfAI = scanner.nextLine();
                while (!typeOfAI.equalsIgnoreCase("-n") && !typeOfAI.equalsIgnoreCase("-s")) {
                    System.out.print("Please enter your option again (-n/-s): ");
                    typeOfAI = scanner.nextLine();
                }

                // if this is indeed our turn
                // then create a corresponding player
                if (typeOfAI.equalsIgnoreCase("-s")) {
                    isSmart = true;
                }

                System.out.println("Successfully joined the queue !!!");
                aiTUI.stopReceivingUserInput();
                clientConnection.sendQueue();
            }


        } else {
            System.out.println("You're not logged in yet.");
        }
    }

    /**
     * Handle NEWGAME command from the server,
     * which is NEWGAME~<pl1_name>~<pl2_name>.
     *
     * Determine a new DotAndBox game with the pre-chosen players.
     */
    public void handleNewGame(String receivedMessage) {
        this.currentState = ClientState.IN_GAME;
        String[] parse = receivedMessage.split("~");
        // name of the 2 players respectively
        String namePlayer1 = parse[1];
        String namePlayer2 = parse[2];

        if (namePlayer1.equals(this.usernameLoggedIn)) {
            System.out.println("You're playing against " + namePlayer2);
        } else {
            System.out.println("You're playing against " + namePlayer1);
        }

        this.isInGame = true;
        this.isQueued = false;


        // check if the first turn belongs to us
        boolean playFirst = namePlayer1.equals(this.usernameLoggedIn);


        System.out.println("Player " + namePlayer1 + " goes first");
        AbstractPlayer otherPlayer;
        if (isBot) {
            if (isSmart && playFirst) {
                this.currentPlayer = new ComputerPlayer(Mark.AA, new SmartStrategy(Mark.AA));
            } else if ((isSmart && !playFirst)) {
                this.currentPlayer = new ComputerPlayer(Mark.BB, new SmartStrategy(Mark.BB));
            } else if (!isSmart && playFirst) {
                this.currentPlayer = new ComputerPlayer(Mark.AA, new NaiveStrategy(Mark.AA));
            } else {
                this.currentPlayer = new ComputerPlayer(Mark.BB, new NaiveStrategy(Mark.BB));
            }
        } else { // human player
            if (playFirst) {
                this.currentPlayer = new HumanPlayer(this.usernameLoggedIn, Mark.AA);
            } else {
                this.currentPlayer = new HumanPlayer(this.usernameLoggedIn, Mark.BB);
            }
        }

        // next, create a game object between the 2 players
        if (playFirst) {
            otherPlayer = new HumanPlayer(namePlayer2, Mark.BB);
            game = new DotsGame(this.currentPlayer, otherPlayer);

        } else {
            otherPlayer = new HumanPlayer(namePlayer1, Mark.AA);
            game = new DotsGame(otherPlayer, this.currentPlayer);
        }

        // then print out the board to observe the state
        System.out.println("Current board:");
        System.out.println(game.getBoard());
    }

    /**
     * Send MOVE command to the server socket
     * by delegating to the clientConnection to do its job.
     *
     * ClientConnection will use the sendMessage() method to
     * send the command MOVE to the server socket with an index of that move.
     */
    //@pure;
    public void doMove() {
        // if this is our turn
        if (game.getTurn() == currentPlayer && isInGame) {

            // then, we'll find a move and send this move
            Move currentMove = this.currentPlayer.determineMove(this.game);
            int row = ((DotsMove) currentMove).getRow();
            int col = ((DotsMove) currentMove).getCol();
            int actualIndex = game.getBoard().index(row, col);

            clientConnection.sendMove(actualIndex);

        } else if (game.getTurn() != currentPlayer) {
            System.out.println("Ain't your turn. Just wait for the other!");
        } else {
            System.out.println("You need to join the queue for game first");
        }
    }

    /**
     * Handle MOVE command from the server,
     * which is MOVE~<N>.
     *
     * Receive the index of the move from server, then place that move to the board.
     */
    public void handleMove(String messageReceived) {
        // the server responses the MOVE
        String[] parse = messageReceived.split(Protocol.SEPARATOR); // MOVE~index
        int index = Integer.parseInt(parse[1]);

        int rowConvert = this.game.getBoard().toRow(index);
        int colConvert = this.game.getBoard().toColumn(index);

        Mark currentMark;
        if (this.game.turnIndex == 0) {
            currentMark = Mark.AA;
        } else {
            currentMark = Mark.BB;
        }

        Move moveToPlaceInCell = new DotsMove(rowConvert, colConvert, currentMark);

        if (game.isValidMove(moveToPlaceInCell)) {
            game.doMove(moveToPlaceInCell);
            System.out.println(this.game.getBoard());
            if (game.isGameover()) {
                System.out.println("Game Over");
//                System.out.println("The winner is: " + game.getWinner());
                this.isInGame = false;
                return;
            }

            System.out.println("It's " + game.getTurn() + "'s turn");
        }

        // continuously check if the next move is our move or not
//        while (game.getTurn() == this.currentPlayer && !this.game.isGameover()) {
//            System.out.println("Your turn");
//            sendMove();
//        }
    }

    public void handleGameOver(String messageReceived) {
        String[] parse = messageReceived.split(Protocol.SEPARATOR);
        String result = parse[1];
        this.isInGame = false;

        switch (result) {
            case Protocol.DISCONNECT:
                System.out.println("Your opponent is disconnected, so you're the winner");
                break;
            case Protocol.DRAW:
                System.out.println("Draw! No winner");
                break;
            case Protocol.VICTORY:
                String winner = parse[2];
                if (winner.equals(usernameLoggedIn)) {
                    winner = "you";
                }
                System.out.println("The winner is " + winner + "!");
        }
    }

}

