package game.ai;

import game.model.Game;
import game.model.Mark;
import game.model.Move;
import game.model.AbstractPlayer;

/**
 * This is the class of a computer player.
 */
public class ComputerPlayer extends AbstractPlayer {
    private final Mark mark;
    private Strategy strategy;

    /**
     * Creates a new ComputerPlayer object.
     *
     * @param strategy the strategy that ComputerPlayer will be using
     * @param mark the mark that computer player uses
     */
    public ComputerPlayer(Mark mark, Strategy strategy) {
        super(strategy.getName() + "-" + mark);
        this.mark = mark;
        this.strategy = strategy;
    }

    /**
     * Get the mark of the current player.
     *
     * @return the mark of the player
     */
    //@ensures \result instanceof Mark;
    //@ensures \result.equals(mark);
    public Mark getMark() {
        return mark;
    }

    /**
     * Get the strategy.
     * @return the strategy
     */
    //@ensures \result instanceof Strategy;
    //@ensures \result.equals(strategy);
    public Strategy getStrategy() {
        return strategy;
    }


    /**
     * Set the strategy.
     * @param strategy the strategy we want to set into
     */
    //@ensures getStrategy().equals(strategy);
    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }

    /**
     * Determine the Move of the player.
     *
     * @param game the current game
     * @return the Move to be determined based on the Strategy that is being used
     */
    //@requires game!=null;
    @Override
    public Move determineMove(Game game) {
       return strategy.determineMove(game);
    }
}
