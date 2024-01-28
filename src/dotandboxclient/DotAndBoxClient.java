package dotandboxclient;
import exception.WrongFormatProtocol;
import game.ai.ComputerPlayer;
import game.ai.NaiveStrategy;
import game.ai.SmartStrategy;
import game.model.*;
import java.io.IOException;
import java.net.InetAddress;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;
import networking.*;
import protocol.Protocol;

public class DotAndBoxClient {
    public static final String gameName = "Resit-8 game";
    private ClientConnection clientConnection;
    private String usernameLoggedIn;
    private AbstractPlayer currentPlayer;
    private DotsGame game;
    private boolean isBot = false;
    private boolean isSmart = false;
    private boolean isLoggedIn;
    private boolean isConnectedToServer;
    private boolean isQueued;
    private boolean isInGame;

//    private List<ClientListener> listeners;

    /**
     * This is the constructor for the Client.
     * @param address the address to connect to
     * @param port the port to connect to
     * @throws IOException
     */
    DotAndBoxClient(InetAddress address, int port) throws IOException {
        this.clientConnection = new ClientConnection(address, port, this);
        this.isConnectedToServer = true;

        this.usernameLoggedIn = null;
        this.isLoggedIn = false;
        this.isQueued = false;
        this.isInGame = false;
    }

    public void confirmIsBot() {
        this.isBot = true;
    }

    public void confirmIsSmart() {
        this.isSmart = true;
    }

    /**
     * Close the connection by calling the handleDisconnect method of the
     * Client connection.
     */
    void close() {
        clientConnection.handleDisconnect();
    }


    /**
     * Send HELLO command to the server socket
     * by delegating to the clientConnection to do its job.
     */
    public void sendHello() {
        this.clientConnection.sendHello();
    }

    /**
     * Handle HELLO command from the server,
     * which is HELLO~<server description>.
     */
    public void handleHello(String receivedMsg) throws WrongFormatProtocol {
        System.out.println("[CLIENT] Handle hello");
        if (receivedMsg.split(Protocol.SEPARATOR).length < 2) {
            throw new WrongFormatProtocol("The command is in wrong format");
        } else {
            new DotAndBoxClientTUI().printMenu();
            System.out.println("In order to start game, you need LOGIN first!");
        }
    }

    /**
     * Send LOGIN command to the server socket
     * by delegating to the clientConnection to do its job.
     */
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
     */
    public void handleLogin(String receivedMessage) {
        if (receivedMessage.equals(Protocol.LOGIN)) { // if the user is not logged in yet
            System.out.println("Logged in as " + this.usernameLoggedIn);
            this.isLoggedIn = true;
        } else {
            System.out.println("You're already logged in / This name has been taken");
            System.out.println("Please choose another option / name");
        }
    }

    public void sendList() {
        if (isLoggedIn) {
            clientConnection.sendList();
        } else { System.out.println("You're not logged in yet."); }
    }

    public void handleList(String receivedMessage) {
        System.out.println(receivedMessage);
        String[] activePlayers = receivedMessage.split("~");
        System.out.print("Active players:");

        for (int i = 1; i < activePlayers.length; i++) {
            System.out.print(" " + activePlayers[i]);
        }
        System.out.println("");
    }

    /**
     * Send QUEUE command to the server socket
     * by delegating to the clientConnection to do its job.
     */
    public void sendQueue() {
        if (isLoggedIn) {
            if (isQueued && !isInGame) { // in queue but not in game
                System.out.println("You're already in a queue! Are you sure you want to leave (Y/N)?");
                Scanner scanner = new Scanner(System.in);
                String answer = scanner.nextLine();

                if (answer.toUpperCase().equals("Y")) {
                    clientConnection.sendQueue();
                    System.out.println("Successfully left the queue !!!");
                    this.isQueued = false;
                }

            } else if (isQueued && isInGame) {
                System.out.println("Cannot queue because you're in a game");
            } else {
                isQueued = true;

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
            }


        } else {
            System.out.println("You're not logged in yet.");
        }
    }

    /**
     * Handle NEWGAME command from the server,
     * which is NEWGAME~<pl1_name>~<pl2_name>.
     *
     */
    public void handleNewGame(String receivedMessage) {
        System.out.println(receivedMessage);
        String[] parse = receivedMessage.split("~");

        this.isInGame = true;
        this.isQueued = false;

        // name of the 2 players respectively
        String namePlayer1 = parse[1];
        String namePlayer2 = parse[2];

        // check if the first turn belongs to us
        boolean playFirst = namePlayer1.equals(this.usernameLoggedIn);

        //        String typeOfPlayer;
        //        String typeOfAI;
        //
        //        // Choose AI or not?
        //        System.out.println("Do you want AI to play for you? (y/n):");
        //        typeOfPlayer = scanner.nextLine();
        //
        //        while (!typeOfPlayer.equalsIgnoreCase("y") && !typeOfPlayer.equalsIgnoreCase("n")) {
        //            System.out.println("Please enter your option again (y/n):");
        //            typeOfPlayer = scanner.nextLine();
        //        }
        //
        //        if (typeOfPlayer.equalsIgnoreCase("y")) {
        //            // Ask which AI
        //            System.out.print("What type (naive/smart) of AI do you want to use (-n/-s)?: ");
        //            typeOfAI = scanner.nextLine();
        //
        //            while (!typeOfAI.equalsIgnoreCase("-n") && !typeOfAI.equalsIgnoreCase("-s")) {
        //                System.out.print("Please enter your option again (-n/-s): ");
        //                typeOfAI = scanner.nextLine();
        //            }
        //
        //            // if this is indeed our turn
        //            // then create a corresponding player
        //            if (playFirst) {
        //                if (typeOfAI.equalsIgnoreCase("-n")) {
        //                    this.currentPlayer = new ComputerPlayer(Mark.AA, new NaiveStrategy(Mark.AA));
        //                } else {
        //                    this.currentPlayer = new ComputerPlayer(Mark.AA, new SmartStrategy(Mark.AA));
        //                }
        //            } else {
        //                if (typeOfAI.equalsIgnoreCase("-n")) {
        //                    this.currentPlayer = new ComputerPlayer(Mark.BB, new NaiveStrategy(Mark.BB));
        //                } else {
        //                    this.currentPlayer = new ComputerPlayer(Mark.BB, new SmartStrategy(Mark.BB));
        //                }
        //            }
        //        } else { // if no bot
        //            if (playFirst) {
        //                this.currentPlayer = new HumanPlayer(this.usernameLoggedIn, Mark.AA);
        //            } else {
        //                this.currentPlayer = new HumanPlayer(this.usernameLoggedIn, Mark.BB);
        //            }
        //        }


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
        System.out.println(game.getBoard());

        // if this is our turn
        if (game.getTurn() == this.currentPlayer) {

            // then, we'll find a move and send this move
            Move currentMove = this.currentPlayer.determineMove(this.game);
            int row = ((DotsMove) currentMove).getRow();
            int col = ((DotsMove) currentMove).getCol();
            int actualIndex = game.getBoard().index(row, col);

            sendMove(actualIndex);

        } else { // else, we'll be waiting
            System.out.println("Waiting for the other's turn!");
        }

    }

    public void sendMove(int index) {
        if (isLoggedIn) {
            if (isInGame) {
                clientConnection.sendMove(index);
            } else { // not in game
                System.out.println("You need to join the queue for game first");
            }
        } else {
            System.out.println("You are not logged in yet");
        }
    }

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
            this.game.doMove(moveToPlaceInCell);
            System.out.println(this.game.getBoard());
            if (this.game.isGameover()) {
                System.out.println("Game Over");
                this.isInGame = false;
            }
        }

        // check if the next move is our move or not
        if (game.getTurn() == this.currentPlayer && !this.game.isGameover()) {
            System.out.println("Your turn");

            Move currentMove = this.currentPlayer.determineMove(this.game);

            if (currentMove == null) {
                System.out.println("No more valid moves.");

            } else { // determine the move and send the move
                int row = ((DotsMove) currentMove).getRow();
                int col = ((DotsMove) currentMove).getCol();
                int actualIndex = this.game.getBoard().index(row, col);

                sendMove(actualIndex);
            }
        } else {
            System.out.println("Waiting for the other's turn!");
        }


    }

}

