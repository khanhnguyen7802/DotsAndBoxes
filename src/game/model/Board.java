package game.model;

import utils.Helper;

/**
 * Board for the BoxAndDot game.
 */

public class Board {

    /*@public invariant ANSI_RED == "\u001B[31m";
    @public invariant ANSI_BLUE == "\033[0;34m";
    @public invariant ANSI_RESET == "\u001B[0m";
    @public invariant ANSI_GREEN == "\033[1;92m";
    @public invariant FULL_VERTICAL == String.valueOf('│');
     */

    public static final int DIM = 5;
    private static final String DELIM = "        ";
    public static final String ANSI_RED = "\u001B[31m";
    public static final String ANSI_BLUE = "\033[0;34m";
    public static final String ANSI_RESET = "\u001B[0m";
    public static final String ANSI_GREEN = "\033[1;92m";
    public static final String FULL_VERTICAL = String.valueOf("│");

    /*@ public invariant (fields.length == DIM * (DIM + 1) * 2);
    @ public invariant (\num_of int i ; 0 <= i && i < DIM * (DIM + 1) * 2;
    fields[i] == Mark.AA) <= 25;
    @ public invariant (\num_of int i ; 0 <= i && i < DIM * (DIM + 1) * 2;
    fields[i] == Mark.BB) <= 25;
    */
    /**
     * The DIM by DIM fields of the Tic Tac Toe board. See NUMBERING for the
     * coding of the fields.
     */

    private final /*@ spec_public */ Mark[] fields;

    /**
     * Constructor to create an empty board.
     */
    /*@ ensures (\forall int i; 0 <= i && i < Board.DIM * (Board.DIM + 1) * 2;
     fields[i] == Mark.EMPTY);
     */
    public Board() {
        int numberOfLines = Board.DIM * (Board.DIM + 1) * 2;

        this.fields = new Mark[numberOfLines];
        for (int i = 0; i < numberOfLines; i++) {
            this.fields[i] = Mark.EMPTY;
        }
    }

    /**
     * Creates a deep copy of this field.
     * @return return a deep copy of a new board
     */
    /*@ ensures \result != this;
     ensures (\forall int i; (i >= 0 && i < Board.DIM * (Board.DIM + 1) * 2);
     \result.fields[i] == this.fields[i]);
     @*/
    public Board deepCopy() {
        Board newBoard = new Board();
        System.arraycopy(this.fields, 0, newBoard.fields, 0,
                         Board.DIM * (Board.DIM + 1) * 2 - 1 + 1);

        return newBoard;
    }

    /**
     * Given the row and col, return the corresponding index.
     * @param row the index of the row
     * @param col the index of the col
     * @return the corresponding index of a field
     */
    //@requires isField(row, col);
    //@pure;
    public int index(int row, int col) {
        if (row % 2 == 0) {
            return (DIM + DIM + 1) * row / 2 + col;
        } else {
            return (row * DIM) + col + (row - 1) / 2;
        }
    }

    /**
     * Given the index, check if that index is valid in the field.
     * @param index the index we want to check
     * @return True if it is a valid field; otherwise False.
     */
    //@ ensures index >= 0 && index < Board.DIM * (Board.DIM + 1) * 2 ==> \result == true;
    public boolean isField(int index) {
        return index >= 0 && index < Board.DIM * (Board.DIM + 1) * 2;
    }

    /**
     * Given row and col, check if they form a valid index in the field.
     * @param row the index of the row
     * @param col the index of the col
     * @return True if it is valid; otherwise False
     */
    /*@ ensures row >= 0 && row <= DIM * 2 && col >= 0 && (col <= DIM - 1 || col <= DIM)
    ==> \result == true;
    */
    public boolean isField(int row, int col) {
        if (row % 2 == 0) {
            return row >= 0 && col >= 0 && row <= DIM * 2 && col <= DIM - 1;
        } else {
            return row >= 0 && col >= 0 && row <= DIM * 2 && col <= DIM;
        }
    }

    /**
     * Returns the content of the field i.
     * @param i the number of the field
     * @return the mark on the field
     */
    /*@ requires isField(i);
    ensures \result == Mark.EMPTY || \result == Mark.BB || \result == Mark.AA;
     @*/
    //@pure;
    public Mark getField(int i) {
        if (isField(i)) {
            return fields[i];
        }

        return null;
    }

    /**
     * Returns the content of the field referred to by the (row,col) pair.
     * @param row the row of the field
     * @param col the column of the field
     * @return the mark on the field
     */
    /*@ requires isField(row, col);
    ensures \result == Mark.EMPTY || \result == Mark.BB
    || \result == Mark.AA || \result == Mark.FILLED;
     @*/
    public Mark getField(int row, int col) {
        int indexConvert = index(row, col);

        return getField(indexConvert);
    }

    /**
     * Returns true if the field[i] is empty.
     * @param i the index of the field
     * @return true if the field is empty
     */
    /*@ requires isField(i);
    ensures getField(i) == Mark.EMPTY ==> \result == true;
     @*/
    public boolean isEmptyField(int i) {
        return isField(i) && fields[i] == Mark.EMPTY;
    }

    /**
     * Returns true if the field referred to by the (row,col) pair it empty.
     * @param row the row of the field
     * @param col the column of the field
     * @return True if the field is empty; otherwise False.
     */
    /*@ requires isField(row, col);
    ensures getField(row, col) == Mark.EMPTY ==> \result == true;
     @*/
    public boolean isEmptyField(int row, int col) {
        int indexConvert = index(row, col);
        return getField(indexConvert) == Mark.EMPTY;
    }

    /**
     * Check if the field has been filled or not.
     * @param i the index of the field
     * @return True if that field has been filled.
     */
    /*@ requires isField(i);
    ensures getField(i) == Mark.FILLED ==> \result == true;
     @*/
    public boolean isMarkedField(int i) {
        return isField(i) && (fields[i] == Mark.FILLED);
    }

    /**
     * Tests if the whole board is full.
     * @return true if all fields are occupied
     */
    /*@ ensures (\forall int i; (i >= 0 && i < Board.DIM * (Board.DIM + 1) * 2);
    fields[i] == Mark.AA || fields[i] == Mark.BB);
    */
    public boolean isFull() {
        for (int i = 0; i < Board.DIM * (Board.DIM + 1) * 2; i++) {
            if (isEmptyField(i)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Given an index, check if the player is able to form a square at that index.
     * If it is able, then set that field to the current player's mark
     * (which means, that particular box belongs to that player)
     *
     * @param index the index of the field
     * @return True if there is a square that has been formed; otherwise false
     */
    /*@ requires isField(index);
    ensures (getField(index) == Mark.FILLED
            && getField(index + DIM) == Mark.FILLED
            && getField(index + DIM + 1) == Mark.FILLED
            && getField(index + DIM + DIM + 1) == Mark.FILLED) ==> \result == true;
     @*/
    public boolean hasSquare(int index) {
        int sq1 = index + DIM;
        int sq2 = index + DIM + 1;
        int sq3 = index + DIM + DIM + 1;
        //if the player has all sides of a box mark the box as the player's box
        return toRow(index) % 2 == 0 && getField(index) == Mark.FILLED && isMarkedField(
                sq1) && isMarkedField(sq2) && (getField(
                sq3) != Mark.EMPTY) && index <= Board.DIM * (Board.DIM + 1) * 2 - 1 - (DIM * 2 + 1);
    }


    /**
     * Returns true if the game is over. The game is over when there is a winner
     * or the whole board is full.
     * @return true if the game is over
     */
    //@ ensures isFull() ==> \result == true;
    public boolean isGameOver() {
        return isFull();
    }

    /**
     * Check if the game is draw or not.
     * @return True if game is draw; otherwise False
     */
    /*@ensures (\num_of int i ; 0 <= i && i < DIM * (DIM + 1) * 2; fields[i] == Mark.AA)
    == (\num_of int i ; 0 <= i && i < DIM * (DIM + 1) * 2; fields[i] == Mark.BB);
    */
    public boolean isDraw() {
        int wins = 0;
        for (int i = 0; i <= (Board.DIM * (Board.DIM + 1) * 2 - 1 - (Board.DIM * 2 + 1)); i++) {
            if (getField(i) == Mark.AA && toRow(i) % 2 == 0) {
                wins++;
                if (wins == (DIM * DIM / 2)) {
                    return true;
                }
            }
        }
        return false;
    }


    /**
     * Checks if the mark m has won. A mark wins if it controls at
     * least one row, column or diagonal.
     * @param m the mark of interest
     * @return true if the mark has won
     */
    /*@ requires m == Mark.BB || m == Mark.AA;
     @*/
    public boolean isWinner(Mark m) {
        int wins = 0;
        for (int i = 0; i <= (Board.DIM * (Board.DIM + 1) * 2 - 1 - (DIM * 2 + 1)); i++) {
            if (getField(i) == m && toRow(i) % 2 == 0) {
                wins++;
                if (wins >= Math.round((float) (DIM * DIM) / 2)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Check if there is a winner at the end of the game.
     * @return true if there is a winner (either A or B); otherwise false.
     */
    //@pure;
    public boolean hasWinner() {
        return isWinner(Mark.AA) || isWinner(Mark.BB);
    }

    /**
     * Returns a String representation of this board. In addition to the current
     * situation, the String also shows the numbering of the fields.
     *
     * @return the game situation as String
     */
    public String toString() {
        String dot = String.valueOf("•"); // unicode hex
        int indexNumbering = 0;
        StringBuilder s = new StringBuilder(); // for both left and right board

        for (int i = 0; i < DIM * 2 + 1; i++) {
            StringBuilder row = new StringBuilder();
            if (i % 2 == 0) { // horizontal row
                // TODO: for the horizontal row on the left
                for (int j = 0; j < DIM + 1; j++) {
                    if (j == DIM) {
                        row.append(dot).append("  ");
                        continue;
                    }

                    String choice = getField(i, j).toString().substring(0, 1);
                    String temporaryRowForHorizontal = "";
                    switch (choice) {
                        case "A":
                            temporaryRowForHorizontal += dot + ANSI_RED + "----" + ANSI_RESET;
                            row.append(temporaryRowForHorizontal);

                            break;
                        case "B":
                            temporaryRowForHorizontal += dot + ANSI_BLUE + "----" + ANSI_RESET;
                            row.append(temporaryRowForHorizontal);

                            break;
                        case "F":
                            temporaryRowForHorizontal += dot + ANSI_GREEN + "----" + ANSI_RESET;
                            row.append(temporaryRowForHorizontal);

                            break;
                        default:
                            row.append(dot).append(" ")
                                    .append(getField(i, j).toString().substring(0, 1)
                                                    .replace("E", " "));

                            row.append("  "); // separate the dots

                    }


                }

                s.append(row).append(DELIM);

                // TODO: for the horizontal row on the right
                for (int k = 0; k < DIM; k++) {
                    String temporaryRowForHorizontal = dot + "    ";
                    String indexStr = Integer.toString(indexNumbering);
                    temporaryRowForHorizontal = Helper.myReplace(temporaryRowForHorizontal,
                                                                 indexStr, 2);

                    s.append(temporaryRowForHorizontal);

                    indexNumbering++;
                }
                s.append(dot); // last dot on the upper line

                s.append("\n");

            } else { // vertical row

                // TODO: for the vertical row on the left
                for (int j = 0; j < DIM + 1; j++) {

                    String choice = getField(i, j).toString().substring(0, 1);
                    String tempVerRow = "";
                    switch (choice) {
                        case "A":
                            if (j == DIM) {
                                tempVerRow += ANSI_RED + FULL_VERTICAL + " " + ANSI_RESET;
                                row.append(tempVerRow);
                                continue;
                            }

                            tempVerRow += ANSI_RED + FULL_VERTICAL + "    " + ANSI_RESET;
                            row.append(tempVerRow);

                            break;
                        case "B":
                            if (j == DIM) {
                                tempVerRow += ANSI_BLUE + FULL_VERTICAL + " " + ANSI_RESET;
                                row.append(tempVerRow);
                                continue;
                            }

                            tempVerRow += ANSI_BLUE + FULL_VERTICAL + "    " + ANSI_RESET;
                            row.append(tempVerRow);
                            break;
                        case "F":
                            if (j == DIM) {
                                tempVerRow += ANSI_GREEN + FULL_VERTICAL + " " + ANSI_RESET;
                                row.append(tempVerRow);
                                continue;
                            }

                            tempVerRow += ANSI_GREEN + FULL_VERTICAL + "    " + ANSI_RESET;
                            row.append(tempVerRow);
                            break;
                        default:
                            if (j == DIM) {
                                row.append(" ").append(getField(i, j).toString().substring(0, 1)
                                                               .replace("E", " "));
                                continue;
                            }

                            row.append("  ").append(getField(i, j).toString().substring(0, 1)
                                                            .replace("E", " "));
                            row.append("  "); // separate the dots

                    }


                }

                s.append(row).append(DELIM); // separate the two boards

                // TODO: for vertical row on the right
                for (int m = 0; m <= DIM; m++) {
                    String indexStr = Integer.toString(indexNumbering);
                    String temporaryRowForVertical = "     ";
                    temporaryRowForVertical = Helper.myReplace(temporaryRowForVertical, indexStr,
                                                               0);

                    s.append(temporaryRowForVertical);


                    indexNumbering++;
                }

                s.append("\n");

            }

        }

        return s.toString();
    }


    /**
     * Empties all fields of this board (i.e., let them refer to the value
     * Mark. EMPTY).
     */
    /*@ ensures (\forall int i; (i >= 0 && i < Board.DIM * (Board.DIM + 1) * 2);
    fields[i] == Mark.EMPTY);
    */
    public void reset() {
        for (int i = 0; i <= Board.DIM * (Board.DIM + 1) * 2 - 1; i++) {
            setField(i, Mark.EMPTY);
        }
    }


    /**
     * Given the index, set the content of field i to the mark m.
     * @param i the field number
     * @param m the mark to be placed
     */
    /*@ requires isField(i);
    ensures getField(i) == m;
     @*/
    public void setField(int i, Mark m) {
        if (isField(i)) {
            fields[i] = m;
        }
    }

    /**
     * Sets the content of the field represented by
     * the (row,col) pair to the mark m.
     * @param row the field's row
     * @param col the field's column
     * @param m the mark to be placed
     */
    /*@ requires isField(row, col);
    ensures getField(row, col) == m;
     @*/
    public void setField(int row, int col, Mark m) {
        fields[index(row, col)] = m;
    }

    /**
     * Given an index of a field, convert to the index of the corresponding row.
     * @param index the index of the field
     * @return the corresponding row for that index
     */
    //@requires isField(index);
    public int toRow(int index) {
        if (index % (DIM * 2 + 1) < DIM) {
            return (index / (DIM + DIM + 1)) * 2;
        } else {
            return (index / (DIM + DIM + 1)) * 2 + 1;
        }
    }

    /**
     * Given an index of a field, convert to the index of the corresponding row.
     * @param index the index of the field
     * @return the corresponding col for that index
     */
    //@requires isField(index);
    public int toColumn(int index) {
        if (index % (DIM * 2 + 1) < DIM) {
            return index - (toRow(index) * (DIM + DIM + 1)) / 2;
        } else {
            return index % (DIM + DIM + 1) - DIM;
        }
    }
}
