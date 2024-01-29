package game.TUI;

import dotandboxclient.ClientListener;
import dotandboxclient.DotAndBoxClient;
import game.ai.ComputerPlayer;
import game.ai.NaiveStrategy;
import game.ai.SmartStrategy;
import game.ai.Strategy;
import game.model.Mark;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.UnknownHostException;
import protocol.Protocol;
import server.ServerConnection;

public class AiTUI implements ClientListener {
    private Strategy strategy = new NaiveStrategy(Mark.EMPTY);
    private DotAndBoxClient dotAndBoxClient;
    //@private invariant keepReading == true || keepReading == false;

    private boolean keepReading;
    BufferedReader in;

    /**
     * A constructor for the TUI.
     */
    public AiTUI() {
        this.keepReading = true;
        this.in = new BufferedReader(new InputStreamReader(System.in));
    }


    public void printMenu() {
        System.out.println("What should the AI be called");
    }

    @Override
    public void connectionLost() {

    }

    /**
     * This is the method to run each AI's TUI.
     * As soon as an AI client is created, run this method to start the client.
     */
    public void runTUI() {
        System.out.println("[AI_TUI] Welcome to the AI");
        InetAddress inetAddress = getAddress();
        int portNumber;
        while (true) {
            portNumber = getPortNumber();

            try {
                dotAndBoxClient = new DotAndBoxClient(inetAddress, portNumber);
                break;
            } catch (IOException e) {
                System.out.println("[AI_TUI] Cannot access the desired port");
            } catch (IllegalArgumentException g) {
                System.out.println("Port number must be within [0, 65535]");
                System.out.println("Please try again");
            }

        }
        System.out.println("[AI_TUI] The AI has connected to server");
        boolean connectedToServer = true;

        // a separate thread is created to read from socket
        dotAndBoxClient.sendHello();
        start();
        dotAndBoxClient.doMove();

        //        while (connectedToServer) {
        //        }
    }

    /**
     * Ask the user and get the address from the user input.
     * @return the address (type InetAddress)
     */
    //@ensures \result instanceof InetAddress;
    public InetAddress getAddress() {
        String ip;
        InetAddress address = null;

        while (address == null) {
            System.out.print("Enter IP Address: ");

            try {
                ip = in.readLine();
                address = InetAddress.getByName(ip);
            } catch (UnknownHostException e) {
                System.out.println("[AI_TUI] Error in getting address - Unknown Host");
            } catch (IOException e) {
                System.out.println("[AI_TUI] Error in getting address - Cannot read input");
            }
        }

        return address;
    }

    /**
     * Ask the user and get the port number from the user input.
     * @return the port number
     */
    public int getPortNumber() {
        System.out.print("Enter port number: ");
        int portNumber;

        try {
            portNumber = Integer.parseInt(in.readLine());
        } catch (IOException e) {
            System.out.println("[AI_TUI] Error in getting port number - Cannot read input");
            System.out.println("Please try again");
            return getPortNumber();
        } catch (NumberFormatException e) {
            System.out.println("[AI_TUI] What port should I connect to?");
            System.out.println("Please try again");
            return getPortNumber();
        }

        return portNumber;
    }

    public enum State{
        InQ, InGame
    }
    public AiTUI.State currentState = AiTUI.State.InQ;

    /**
     * Handle the commands that user types in.
     * As soon as the system receives the commands from user input,
     * send those to the server to handle accordingly
     */
    public void handleInputCommands() {
        String input = "";

        try {
            input = in.readLine();
        } catch (IOException e) {
            System.out.println("[AI_TUI] Error in getting input from user");
        }

        String[] parse = input.split("\\s+");
        String command = parse[0];

        switch (command) {
            case Protocol.LOGIN:
                String username = parse[1];
                if (parse.length == 2) { // LOGIN <name>
                    username = parse[1];
                } else if (parse.length > 2) { // LOGIN <first> <last> <blabla>
                    for (int i = 1; i < parse.length; i++) {
                        username += parse[i];
                    }
                }
                dotAndBoxClient.sendLogin(username);
                dotAndBoxClient.sendQueueAI();
                currentState = State.InGame;
                break;
            default:
                System.out.println("Command is not recognized! Please choose again");
                handleInputCommands();
        }

    }

    public void start() {
        while (keepReading) {
            try {
                handleInputCommands();
            } catch (RuntimeException e) {
                System.out.println("[AI_TUI] Runtime exception");
            }
        }
    }

    //@ensures keepReading == false;
    public void stopReceivingUserInput() {
        this.keepReading = false;
    }

    /**
     * Main function to run the TUI.
     * @param args parameters
     */
    public static void main(String[] args) {
        new AiTUI().runTUI();
    }
}