package game.ai;

import game.model.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class SmartStrategy implements Strategy{
    private Random rand = new Random();

    private final Mark mark;
    public SmartStrategy(Mark mark){
        this.mark = mark;

    }

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
     * @param game - current state of the game
     * @return the naive valid move
     */

        @Override
        public Move determineMove(Game game) {
            List<Move> possibleMoves = game.getValidMoves();
            Board board1 = ((DotsGame) game).getBoard().deepCopy();


            List<Move> hasSq = new ArrayList<>();
            List<Move> noSq = new ArrayList<>();

            for (int j = 0; j <= ((Board.DIM*(Board.DIM+1)*2-1));j++){
                if(board1.toRow(j) % 2 == 0 && board1.hasSquare(j)){
                    if(possibleMoves.contains(new DotsMove(board1.toRow(j), board1.toColumn(j), Mark.EMPTY))){
                    hasSq.add(new DotsMove(board1.toRow(j), board1.toColumn(j), Mark.EMPTY));}
                    else if (possibleMoves.contains(j+Board.DIM)) {
                        hasSq.add(new DotsMove(board1.toRow(j+Board.DIM), board1.toColumn(j+Board.DIM), Mark.EMPTY));
                    } else if (possibleMoves.contains(j+Board.DIM + 1)) {
                        hasSq.add(new DotsMove(board1.toRow(j+Board.DIM + 1), board1.toColumn(j+Board.DIM + 1), Mark.EMPTY));
                    } else if (possibleMoves.contains(j+Board.DIM*2+1)) {
                        hasSq.add(new DotsMove(board1.toRow(j+Board.DIM*2+1), board1.toColumn(j+Board.DIM*2+1), Mark.EMPTY));
                    }
                } else {
                    noSq.add(new DotsMove(board1.toRow(j), board1.toColumn(j), Mark.EMPTY));
                }
            }
            System.out.println(hasSq.size());

            if (!hasSq.isEmpty() && rand.nextBoolean()) {
                int index = rand.nextInt(hasSq.size());
                return hasSq.get(index);
            } else if (!noSq.isEmpty()) {
                int index = rand.nextInt(noSq.size());
                return noSq.get(index);
            }

            return null;
        }


}
