package game.model;

import java.util.Scanner;

/**
 * This is the class for a Human Player.
 */
public class HumanPlayer extends AbstractPlayer {
    private Mark mark;
//    private String name;


    /**
     * Creates a new Player object.
     *
     * @param name name of the player
     */
    public HumanPlayer(String name, Mark mark) {
        super(name);
        this.mark = mark;
    }

    /**
     * Get the mark of the current player.
     *
     * @return the mark of the player
     */
    //@pure;
    public Mark getMark() {
        return mark;
    }


    /**
     * Asking for the move on console.
     *
     * @return the move to be determined
     */
    //@ensures game.getValidMoves().contains(\result);
    //@requires game != null;
    @Override
    public Move determineMove(Game game) {
        DotsGame dotsGame = (DotsGame) game;
        Board currentBoard = dotsGame.getBoard();

        while (true) {
            Scanner scanner = new Scanner(System.in);
            System.out.println("Enter a valid move (index): ");
            String number = scanner.next();

            while (!number.matches("-?\\d+(\\.\\d+)?")) {
                System.out.println("Index is not valid! Enter again");
                number = scanner.nextLine();
            }
            int indexMove = Integer.parseInt(number);
            int rowMove = currentBoard.toRow(indexMove);
            int colMove = currentBoard.toColumn(indexMove);
            Move move = new DotsMove(rowMove, colMove, getMark());
            if (game.isValidMove(move)) {
                return move;
            } else System.out.println("Move is not valid! Please enter again!");

        }

    }
}
