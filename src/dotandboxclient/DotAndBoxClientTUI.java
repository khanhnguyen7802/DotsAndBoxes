package dotandboxclient;

import game.ai.ComputerPlayer;
import game.ai.NaiveStrategy;
import game.ai.SmartStrategy;
import game.model.HumanPlayer;
import game.model.Mark;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Scanner;
import protocol.Protocol;

public class DotAndBoxClientTUI implements ClientListener {
    private DotAndBoxClient dotAndBoxClient;
    private boolean keepReading;
    BufferedReader in;

    /**
     * A constructor for the TUI.
     */
    public DotAndBoxClientTUI() {
        this.keepReading = true;
        this.in = new BufferedReader(new InputStreamReader(System.in));
    }

    @Override
    public void printMenu() {
        System.out.println("=================MENU================\n");
        System.out.println("\t1. LOGIN <username>\n");
        System.out.println("\t2. LIST\n");
        System.out.println("\t3. QUEUE\n");
        System.out.println("\t4. MOVE <index>\n");
        System.out.println("\t5. HELP\n");
        System.out.println("\t6. QUIT\n");
        System.out.println("=====================================\n");
        System.out.println("Type in your command in the above syntax:");

    }

    @Override
    public void connectionLost() {

    }


    public void runTUI() {
        System.out.println("[CLIENT_TUI] Start runTUI()");
        InetAddress inetAddress = getAddress();
        int portNumber;
        while (true) {
            portNumber = getPortNumber();

            try {
                dotAndBoxClient = new DotAndBoxClient(inetAddress, portNumber);
                break;
            } catch (IOException e) {
                System.out.println("[CLIENT_TUI] Cannot access the desired port");
            } catch (IllegalArgumentException g) {
                System.out.println("Port number must be within [0, 65535]");
                System.out.println("Please try again");
            }

        }
        System.out.println("[CLIENT_TUI] Client connected to server");
        boolean connectedToServer = true;

        // a separate thread is created to read from socket
        dotAndBoxClient.sendHello();

        while(connectedToServer) {
            System.out.println("1");
            start();
        }
    }

    public InetAddress getAddress() {
        String ip;
        InetAddress address = null;

        while (address == null) {
            System.out.print("Enter IP Address: ");

            try {
                ip = in.readLine();
                address = InetAddress.getByName(ip);
            } catch (UnknownHostException e) {
                System.out.println("[CLIENT_TUI] Error in getting address - Unknown Host");
            } catch (IOException e) {
                System.out.println("[CLIENT_TUI] Error in getting address - Cannot read input");
            }
        }

        return address;
    }

    public int getPortNumber() {
        System.out.print("Enter port number: ");
        int portNumber;

        try {
            portNumber = Integer.parseInt(in.readLine());
        } catch (IOException e) {
            System.out.println("[CLIENT_TUI] Error in getting port number - Cannot read input");
            System.out.println("Please try again");
            return getPortNumber();
        } catch (NumberFormatException e) {
            System.out.println("[CLIENT_TUI] Port number should be a number");
            System.out.println("Please try again");
            return getPortNumber();
        }

        return portNumber;
    }

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
            System.out.println("[CLIENT_TUI] Error in getting input from user");
        }

        String[] parse = input.split("\\s+");
        String command = parse[0];

        switch(command) {
            case Protocol.LOGIN:
                String username = "";
                if (parse.length == 2) { // LOGIN <name>
                    username = parse[1];
                }
                else if (parse.length > 2) { // LOGIN <first> <last> <blabla>
                    for (int i = 1; i < parse.length; i++) {
                        username += parse[i];
                    }
                }
                dotAndBoxClient.sendLogin(username);
                break;
            case Protocol.LIST:
                dotAndBoxClient.sendList();
                break;
            case Protocol.QUEUE:
                dotAndBoxClient.sendQueue();
                break;
            case Protocol.MOVE:
                int index = Integer.parseInt(parse[1]);
                dotAndBoxClient.sendMove(index);
                break;
            case "HELP":
                printMenu();
                break;
            case "EXIT":
//                client.closeEverything();
                stopReceivingInput();
                System.out.println("Exited successfully! See you again!");
                break;
            default:
                System.out.println("Command is not recognized! Please choose again");
        }
    }

    public void start() {
        while (keepReading) {
            try {
                handleInputCommands();
            } catch (RuntimeException e) {
                System.out.println("[CLIENT_TUI] Runtime exception");
            }
        }
        this.keepReading = true;
    }

    public void stopReceivingInput() {
        this.keepReading = false;
    }

    public static void main(String[] args) {
        new DotAndBoxClientTUI().runTUI();
    }

}
