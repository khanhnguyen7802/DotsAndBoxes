package game.ai;

import game.model.Board;
import game.model.Game;
import game.model.Mark;
import game.model.Move;
import java.util.List;
import java.util.Random;

public class SmartStartegy implements Strategy{

    private final Mark mark;
    public SmartStartegy(Mark mark){
        this.mark = mark;

    }

    @Override
    public String getName() {
        return "Naive";
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
     * @param game - current state of the game
     * @return the naive valid move
     */
    @Override
    public Move determineMove(Game game) {
        Board board = new Board();
        Board board1= board.deepCopy();
        Random rand = new Random();
        int index = 0;
        List<Move> possibleMoves = game.getValidMoves();
        int moves = 0;
        if(moves > Board.DIM*3){
            if(Board.DIM*Board.DIM - moves % 2 == 0){
                while(board.hasSquare(index, Mark.FILLED)) {
                    index = rand.nextInt(possibleMoves.size());
                    Move thisMove = possibleMoves.get(index);
                    if (!board.hasSquare(index, Mark.FILLED)) {
                        moves++;
                        return thisMove;
                    }
                }
            }
            else {
                while (!board.hasSquare(index, Mark.FILLED)) {
                    index = rand.nextInt(possibleMoves.size());
                    Move thisMove = possibleMoves.get(index);
                    if (board.hasSquare(index, Mark.FILLED)) {
                        moves++;
                        return thisMove;
                    }
                }
            }

        }


        while(board.hasSquare(index, Mark.FILLED)){
            index = rand.nextInt(possibleMoves.size());
            Move randomMove = possibleMoves.get(index);
            if(!board.hasSquare(index, Mark.FILLED))
                moves++;
                return randomMove;
        }
        return null;
    }

}
