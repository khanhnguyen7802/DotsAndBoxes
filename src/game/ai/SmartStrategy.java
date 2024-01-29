package game.ai;

import game.model.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * This class is the Smart Strategy of ComputerPlayer.
 */
public class SmartStrategy implements Strategy {
    private final Random rand = new Random();

    private final Mark mark;
    private int moves = 0;

    public SmartStrategy(Mark mark) {
        this.mark = mark;
    }

    /**
     * Get the name of the strategy.
     * @return name of the strategy
     */
    //@ensures \result.equals("Smart");
    @Override
    public String getName() {
        return "Smart";
    }

    /**
     * Get the mark of the current player.
     *
     * @return the mark of the player
     */
    //@ensures \result instanceof Mark;
    public Mark getMark() {
        return mark;
    }


    /**
     * Keep searching for the valid move until it finds one.
     * The smart strategy doesn't fill in the square that makes it lose.
     *
     * @param game - current state of the game
     * @return the naive valid move
     */
    //@ensures game.getValidMoves().contains(\result);
    @Override
    public Move determineMove(Game game) {
        long start = System.currentTimeMillis();
        long end = start + 2000;
        int index;
        List<Move> possibleMoves = game.getValidMoves();
        while (System.currentTimeMillis() < end) {

            Board board1 = ((DotsGame) game).getBoard().deepCopy();


            List<Move> hasSq = new ArrayList<>();
            List<Move> noSq = new ArrayList<>();

            findMoves(game, board1, hasSq, noSq);
            if (noSq.isEmpty()) {
                if (!((Board.DIM * Board.DIM - moves) % 2 == 0)) {
                    //it checks how many turns are left
                    if (!hasSq.isEmpty()) {
                        // Make random move to potentially complete a square
                        index = rand.nextInt(hasSq.size());
                        Move thisMove = hasSq.get(index);
                        moves++;
                        return thisMove;
                    }

                    // If there are moves that don't complete a square, prioritize them
                    index = rand.nextInt(possibleMoves.size());
                    Move noMove = possibleMoves.get(index);
                    moves++;
                    return noMove;
                }
            }
            if (!hasSq.isEmpty() || (((Board.DIM * Board.DIM - moves) % 2 == 0) && noSq.isEmpty())) {
                // Make random move to potentially complete a square
                index = rand.nextInt(hasSq.size());
                Move thisMove = hasSq.get(index);
                moves++;
                return thisMove;
            }

            // If there are moves that don't complete a square, prioritize them
            index = rand.nextInt(noSq.size());
            Move noSqMove = noSq.get(index);
            moves++;
            return noSqMove;
        }
        // If the AI thinks too long return a random possible move
        index = rand.nextInt(possibleMoves.size());
        Move noSqMove = possibleMoves.get(index);
        moves++;
        return noSqMove;
    }

    private void findMoves(Game game, Board board1, List<Move> hasSq, List<Move> noSq) {
        for (int j = 0; j <= (Board.DIM * (Board.DIM + 1) * 2 - 1); j++) {
            //iterate through each line of the game
            for (int i = 0; i <= (Board.DIM * (Board.DIM + 1) * 2 - 1); i++) {
                //test if after filling in any lines, if it will get a box
                board1.setField(i, Mark.FILLED);
                if (board1.toRow(j) % 2 == 0 && board1.hasSquare(j)) {
                    //if it will get a box chose that option as the possible move
                    if (board1.toRow(j) % 2 == 0 && board1.hasSquare(j)) {
                        board1 = ((DotsGame) game).getBoard().deepCopy();
                        if (game.isValidMove(
                                //check if the option is the top side of the box
                                new DotsMove(board1.toRow(j), board1.toColumn(j), getMark()))) {
                            hasSq.add(new DotsMove(board1.toRow(j), board1.toColumn(j), getMark()));
                        }//check if the option is the left side of the box
                        else if (game.isValidMove(new DotsMove(board1.toRow(j + Board.DIM),
                                                               board1.toColumn(j + Board.DIM),
                                                               getMark()))) {
                            hasSq.add(new DotsMove(board1.toRow(j + Board.DIM),
                                                   board1.toColumn(j + Board.DIM), getMark()));
                        } //check if it's the right side of the box
                        else if (game.isValidMove(new DotsMove(board1.toRow(j + Board.DIM + 1),
                                                               board1.toColumn(j + Board.DIM + 1),
                                                               getMark()))) {
                            hasSq.add(new DotsMove(board1.toRow(j + Board.DIM + 1),
                                                   board1.toColumn(j + Board.DIM + 1), getMark()));
                        }//check if it's the bottom of the box
                        else if (game.isValidMove(new DotsMove(board1.toRow(j + Board.DIM * 2 + 1),
                                                               board1.toColumn(
                                                                       j + Board.DIM * 2 + 1),
                                                               getMark()))) {
                            hasSq.add(new DotsMove(board1.toRow(j + Board.DIM * 2 + 1),
                                                   board1.toColumn(j + Board.DIM * 2 + 1),
                                                   getMark()));
                        }
                        // at the end of the correct if statement add the possible move to the
                        // hasSQ as after completing one of these moves the AI will have a box
                        break;
                    } else {
                        if (game.isValidMove(
                                //if the move did not yield a box store it in noSq
                                new DotsMove(board1.toRow(j), board1.toColumn(j), getMark()))) {
                            noSq.add(new DotsMove(board1.toRow(j), board1.toColumn(j), getMark()));
                        }
                    }
                }
                // set the temporary board back to its initial state where we haven't
                //tried filling it in
                board1 = ((DotsGame) game).getBoard().deepCopy();
            }
        }
    }


}
