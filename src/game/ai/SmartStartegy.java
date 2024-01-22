package game.ai;

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
        List<Move> possibleMoves = game.getValidMoves();
        return null;
    }
}
