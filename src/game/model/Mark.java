package game.model;

/**
 * Represents a mark in Dots and Boxes game. There three possible values:
 * Mark. AA, Mark. BB, Mark.EMPTY and Mark.FILLED.
 */
public enum Mark {
    EMPTY, AA, BB, FILLED;

    /**
     * Returns the other mark.
     * @return the other mark is this mark is not EMPTY
     */
    //@ ensures this == AA ==> \result == BB && this == BB ==> \result == AA;
    public Mark other() {
        if (this == AA) {
            return BB;
        } else if (this == BB) {
            return AA;
        } else if (this == FILLED) {
            return AA;
        } else {
            return EMPTY;
        }
    }
}
