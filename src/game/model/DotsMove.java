package game.model;

/**
 * Represent a move in the game, i.e.,
 * store the mark to place and the location to place it.
 */
public record DotsMove(int row, int col, Mark mark) implements Move {
    /**
     * Constructor to initialize a specific Mark.
     *
     * @param row  - row of the current move
     * @param col  - column of the current move
     * @param mark - what the mark of the current move is
     */
    public DotsMove {
    }

    /**
     * Get the mark of the current move.
     *
     * @return the current mark of the move
     */
    //@pure;
    @Override
    public Mark mark() {
        return mark;
    }

    /**
     * Get the row of the current move.
     *
     * @return the row accordingly.
     */
    //@pure;
    @Override
    public int row() {
        return row;
    }

    /**
     * Get the column of the current move.
     *
     * @return the column accordingly.
     */
    //@pure;
    @Override
    public int col() {
        return col;
    }


    /**
     * toString() method to print out the info of the current move.
     *
     * @return a formatted String indicating the current move.
     */
    public String toString() {
        return "Row " + this.row + " - Col " + this.col + " - Mark " + this.mark;
    }
}
