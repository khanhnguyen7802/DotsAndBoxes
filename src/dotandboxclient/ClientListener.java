package dotandboxclient;

public interface ClientListener {
    /**
     * This method is to print out the menu with options to be chosen.
     * Option 1: Send the LOGIN protocol to the server -> to log in with your name
     * Option 2: Send the LIST protocol to the server -> to receive a list of all players
     * Option 3: Send the QUEUE protocol to the server -> to participate in a game; if sent twice then leave
     * Option 4: Send the MOVE protocol to the server -> to indicate which move to play
     * Option 5: Print out the help menu that displays options to choose
     * Option 6: Quit the program
     */
    void printMenu();

    //    /**
    //     * Choose a number corresponding to the command
    //     * @return an integer that indicates the corresponding option
    //     */
    //    int chooseCommand();

    /**
     * Dealing with connection lost.
     */
    void connectionLost();

    void printToConsole(String s);
}
