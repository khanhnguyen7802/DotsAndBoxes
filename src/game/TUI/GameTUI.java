package game.TUI;

import game.ai.ComputerPlayer;
import game.ai.NaiveStrategy;
import game.ai.SmartStrategy;
import game.ai.Strategy;
import game.model.*;
import java.util.Scanner;

public class GameTUI {
    private DotsGame game;
    private DotsMove move;
    private AbstractPlayer player1;
    private AbstractPlayer player2;
    private Strategy strategy = new NaiveStrategy(Mark.EMPTY);
    private ComputerPlayer dummy = new ComputerPlayer(Mark.EMPTY, strategy);

    public static void main(String[] args) {
        GameTUI dotsTUI = new GameTUI();
        dotsTUI.run();
    }


    /**
     * Start the game.
     */
    public void run() {
        boolean playAgain = true;
        System.out.println("WELCOME TO TicTacToe");
        Scanner input = new Scanner(System.in);
        System.out.print("Enter name for player 1: ");
        String pl1 = input.nextLine();

        if(pl1.equals("-N")) {
            player1 = new ComputerPlayer(Mark.AA, new NaiveStrategy(Mark.AA));
        }
        if(pl1.equals("-S")) {
            player1 = new ComputerPlayer(Mark.AA, new SmartStrategy(Mark.AA));
        }
        if(player1 == null) {
            player1 = new HumanPlayer(pl1, Mark.AA);
        }


        System.out.print("Enter name for player 2: ");
        String pl2 = input.nextLine();

        if(pl2.equals("-N")) {
            player2 = new ComputerPlayer(Mark.BB, new NaiveStrategy(Mark.BB));
        }
        if(pl2.equals("-S")) {
            player2 = new ComputerPlayer(Mark.BB, new SmartStrategy(Mark.BB));
        }
        if(player2 == null) {
            player2 = new HumanPlayer(pl2, Mark.BB);
        }

        game = new DotsGame(player1, player2);

        while(playAgain) {
            while (!game.isGameover()) {
                System.out.println(game.getBoard()); // current state of the game
                if(game.getTurn().getClass() == dummy.getClass()){
                    ComputerPlayer currentPlayer = (ComputerPlayer) game.getTurn();
                    System.out.println("It's " + currentPlayer.getName() + " turn");
                    Move determinedMove = currentPlayer.determineMove(game); // get the move
                    game.doMove(determinedMove);
                }
                else {

                    HumanPlayer currentPlayer = (HumanPlayer) game.getTurn(); // current player
                    System.out.println("It's " + currentPlayer.getName() + " turn");

                    Move determinedMove = currentPlayer.determineMove(game); // get the move
                    game.doMove(determinedMove);
                }
            }

            System.out.println(game.getBoard());
            if (game.getBoard().hasWinner()) {
                System.out.println("The winner is: " + game.getWinner());
            } else {
                System.out.println("The game ends in a draw");
            }

            System.out.print("Do u want to play again? (yes/no): ");
            Scanner sc = new Scanner(System.in);
            String answer = sc.nextLine();
            if (answer.equals("no"))
                playAgain = false;

            game.getBoard().reset();
        }
    }
}
