package game.ai;

import java.util.List;
import java.util.Random;
import game.model.Game;
import game.model.Mark;
import game.model.Move;

/**
 * This class is the NaiveStrategy of ComputerPlayer.
 */
public class NaiveStrategy implements Strategy {
    private final Mark mark;

    public NaiveStrategy(Mark mark) {
        this.mark = mark;
    }

    /**
     * Get the name of the strategy (in this case, Naive).
     * @return the name of Naive strategy
     */
    //@ensures \result.equals("Naive");
    @Override
    public String getName() {
        return "Naive";
    }

    /**
     * Get the mark of the current player.
     *
     * @return the mark of the player
     */
    //@ensures getMark().equals(mark);
    //@ensures \result instanceof Mark;
    public Mark getMark() {
        return mark;
    }


    /**
     * Keep searching for the valid move until it finds one.
     * @param game - current state of the game
     * @return the naive valid move
     */
    //@requires game != null;
    //@ensures game.getValidMoves().contains(\result);
    //@ensures \result instanceof Move;
    @Override
    public Move determineMove(Game game) {
        List<Move> possibleMoves = game.getValidMoves();
        Random rand = new Random();
        int index = rand.nextInt(possibleMoves.size());
        Move randomMove = possibleMoves.get(index);

        return randomMove;
    }
}
