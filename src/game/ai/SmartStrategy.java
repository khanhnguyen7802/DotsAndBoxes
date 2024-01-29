package game.ai;

import game.model.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * This class is the Smart Strategy of ComputerPlayer.
 */
public class SmartStrategy implements Strategy{
    private Random rand = new Random();

    private final Mark mark;
    public SmartStrategy(Mark mark){
        this.mark = mark;

    }

    /**
     * Get the name of the strategy.
     * @return name of the strategy
     */
    @Override
    public String getName() {
        return "Smart";
    }

    /**
     * Get the mark of the current player.
     *
     * @return the mark of the player
     */
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
    @Override
    public Move determineMove(Game game) {

        int index = 0;
        int moves = 0;
        List<Move> possibleMoves = game.getValidMoves();
        Board board1 = ((DotsGame) game).getBoard().deepCopy();


        List<Move> hasSq = new ArrayList<>();
        List<Move> noSq = new ArrayList<>();

        for (int j = 0; j <= ((Board.DIM * (Board.DIM + 1) * 2 - 1)); j++) {
            for (int i = 0; i <= ((Board.DIM * (Board.DIM + 1) * 2 - 1)); i++){
                board1.setField(i, Mark.FILLED);
                if(board1.toRow(j) % 2 == 0 && board1.hasSquare(j)){
                    if (board1.toRow(j) % 2 == 0 && board1.hasSquare(j)) {
                        board1 = ((DotsGame) game).getBoard().deepCopy();
                        if (game.isValidMove(
                                new DotsMove(board1.toRow(j), board1.toColumn(j), getMark()))) {
                            hasSq.add(new DotsMove(board1.toRow(j), board1.toColumn(j), getMark()));
                        } else if (game.isValidMove(new DotsMove(board1.toRow(j + Board.DIM),
                                                                 board1.toColumn(j + Board.DIM), getMark()))) {
                            hasSq.add(new DotsMove(board1.toRow(j + Board.DIM),
                                                   board1.toColumn(j + Board.DIM), getMark()));
                        } else if (game.isValidMove(new DotsMove(board1.toRow(j + Board.DIM + 1),
                                                                 board1.toColumn(j + Board.DIM + 1),
                                                                 getMark()))) {
                            hasSq.add(new DotsMove(board1.toRow(j + Board.DIM + 1),
                                                   board1.toColumn(j + Board.DIM + 1), getMark()));
                        } else if (game.isValidMove(
                                new DotsMove(board1.toRow(j + Board.DIM * 2 + 1),
                                             board1.toColumn(j + Board.DIM * 2 + 1), getMark()))) {
                            hasSq.add(new DotsMove(board1.toRow(j + Board.DIM * 2 + 1),
                                                   board1.toColumn(j + Board.DIM * 2 + 1),
                                                   getMark()));
                        }
                        break;
                    } else {
                        if (game.isValidMove(
                                new DotsMove(board1.toRow(j), board1.toColumn(j), getMark()))) {
                            noSq.add(new DotsMove(board1.toRow(j), board1.toColumn(j), getMark()));
                        }
                    }
            }
                board1 = ((DotsGame) game).getBoard().deepCopy();
            }
        }
        if (noSq.isEmpty()) {
            if (!(Board.DIM * Board.DIM - moves % 2 == 0)) { //it checks how many turns are left
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
        if (!hasSq.isEmpty() || ((Board.DIM * Board.DIM - moves % 2 == 0) && noSq.isEmpty())) {
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


}
