package game.ai;

import game.model.Board;
import game.model.Game;
import game.model.Mark;
import game.model.Move;
import java.util.List;
import java.util.Random;

public class SmartStrategy implements Strategy{

    private final Mark mark;
    public SmartStrategy(Mark mark){
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
        int pos = possibleMoves.size();
        int moves = 0;
        if(moves > Board.DIM*3){ // the ai does random moves until it doesn't matter
            if(Board.DIM*Board.DIM - moves % 2 == 0){ //it checks how many turns are left from the game
                while(board.hasSquare(index)) {
                    index = rand.nextInt(possibleMoves.size());
                    Move thisMove = possibleMoves.get(index);
                    pos--; // it checks if there are any possible moves that are beneficial
                    if (!board.hasSquare(index)) {
                        moves++;
                        return thisMove;
                    }
                    else if(pos == 0){ //if there are no beneficial moves it returns a random move
                        return thisMove;
                    }
                }
            }
            else { // if the game has an odd number of moves it will fill in a sqaure to make advantage
                while (!board.hasSquare(index)) {
                    index = rand.nextInt(possibleMoves.size());
                    Move thisMove = possibleMoves.get(index);
                    pos--;
                    if (board.hasSquare(index)) {
                        moves++;
                        return thisMove;
                    }else if(pos == 0){
                        return thisMove;
                    }
                }
            }

        }
        //until the it matters the game does random moves
        while(board.hasSquare(index)){
            index = rand.nextInt(possibleMoves.size());
            Move randomMove = possibleMoves.get(index);
            if(!board.hasSquare(index)) {
                moves++;
                pos--;
                return randomMove;
            }else if(pos == 0){
                return randomMove;
            }
        }
        return null;
    }

}
