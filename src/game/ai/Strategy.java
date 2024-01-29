package game.ai;

import game.model.Game;
import game.model.Move;

/**
 * The interface of Strategy. It's an interface for both smart and naive strategy to implement.
 */
public interface Strategy {
    /**
     * Return the name of the strategy.
     *
     * @return the name of the strategy
     */
    //@ensures \result != null;
    //@ensures \result == getName();
    String getName();

    /**
     * Return a next legal move, given the current state of the game.
     *
     * @param game - current state of the game
     * @return a next legal move
     */
    //@ensures \result != null;
    //@requires game!=null;
    //@ensures game.isValidMove(\result);
    Move determineMove(Game game);
}