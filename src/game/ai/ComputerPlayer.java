package game.ai;

import game.model.Game;
import game.model.Mark;
import game.model.Move;
import game.model.AbstractPlayer;


public class ComputerPlayer extends AbstractPlayer {
    private final Mark mark;
    private Strategy strategy;

    /**
     * Creates a new ComputerPlayer object.
     *
     * @param strategy
     * @param mark
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
    public Mark getMark() {
        return mark;
    }

    /**
     * Get the strategy.
     * @return the strategy
     */
    public Strategy getStrategy() {
        return strategy;
    }


    /**
     * Set the strategy.
     * @param strategy the strategy we want to set into
     */
    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }

    @Override
    public Move determineMove(Game game) {
       return strategy.determineMove(game);
    }
}
