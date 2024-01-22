package game.model;

import utils.Helper;

/**
 * Board for the BoxAndDot game.
 */

public class Board {
    /**
     * Dimension of the board, i.e., if set to 5, the board has 5 rows and 5-6 columns.
     */
    public static final int DIM = 5;
    private static final String DELIM = "        ";


    //@ public invariant (fields.length == DIM*DIM);
    //@ public invariant (\num_of int i ; 0 <= i && i < DIM*DIM; fields[i] == Mark.AA) <= 5;
    //@ public invariant (\num_of int i ; 0 <= i && i < DIM*DIM; fields[i] == Mark.BB) <= 5;

    //@ public invariant (\num_of int i;  0 <= i && i < DIM*DIM;fields[i] == Mark.AA) >= (\num_of int i;  0 <= i && i < DIM*DIM; fields[i] == Mark.BB);

    /**
     * The DIM by DIM fields of the Tic Tac Toe board. See NUMBERING for the
     * coding of the fields.
     */

    private /*@ spec_public */ Mark[] fields;
    Board board;
    /**
     * Constructor to create an empty board.
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
     */
    /*@ ensures \result != this;
     ensures (\forall int i; (i >= 0 && i < DIM*DIM); \result.fields[i] == this.fields[i]);
     @*/
    public Board deepCopy() {
        Board newBoard = new Board();
        for (int i = 0; i < Board.DIM * (Board.DIM + 1) * 2 - 1; i++) {
            newBoard.fields[i] = this.fields[i];
        }

        return newBoard;
    }

    /**
     * Given the row and col, return the corresponding index.
     * @param row the index of the row
     * @param col the index of the col
     * @return the corresponding index of a field
     */
    public int index(int row, int col) {
        if (row % 2 == 0) {
            return (DIM + DIM + 1) * row/2 + col;
        } else {
            return (row * DIM) + col + (row - 1)/2;
        }
    }

    /**
     * Given the index, check if that index is valid in the field.
     * @param index the index we want to check
     * @return True if it is a valid field; otherwise False.
     */
    public boolean isField(int index) {
        return index >= 0 && index < Board.DIM * (Board.DIM + 1) * 2;
    }

    /**
     * Given row and col, check if they form a valid index in the field.
     * @param row the index of the row
     * @param col the index of the col
     * @return True if it is valid; otherwise False
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
    public Mark getField(int i) {
        if (isField(i))
            return fields[i];

        return null;
    }

    /**
     * Returns the content of the field referred to by the (row,col) pair.
     * @param row the row of the field
     * @param col the column of the field
     * @return the mark on the field
     */
    /*@ requires isField(row, col);
    ensures \result == Mark.EMPTY || \result == Mark.BB || \result == Mark.AA;
     @*/
    public Mark getField(int row, int col) {
        int indexConvert = index(row, col);

        return getField(indexConvert);
    }

    /**
     * Returns true if the field[i] is empty.
     * @param i the index of the field (see NUMBERING)
     * @return true if the field is empty
     */
    /*@ requires isField(i);
    ensures getField(i) == Mark.EMPTY ==> \result == true;
     @*/
    public boolean isEmptyField(int i) {
        if (isField(i) && fields[i] == Mark.EMPTY)
            return true;

        return false;
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
    public boolean isMarkedField(int i) {
        if (isField(i) && fields[i] == Mark.FILLED)
            return true;

        return false;
    }

    /**
     * Tests if the whole board is full.
     * @return true if all fields are occupied
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM*DIM); fields[i] == Mark.AA || fields[i] == Mark.BB);
    public boolean isFull() {
    	 for (int i = 0; i < Board.DIM * (Board.DIM + 1) * 2; i++) {
             if (isEmptyField(i))
                 return false;
         }
         return true;
    }

    /**
     * Given an index, check if the player is able to form a square at that index.
     * If it is able, then set that field to the current player's mark
     * (which means, that particular box belongs to that player)
     *
     * @param index the index of the field
     * @param m the mark of the current player to set that field to
     * @return True if
     */
    public boolean hasSquare(int index, Mark m){
        int sq1 = index + DIM;
        int sq2 = index + DIM +1;
        int sq3 = index + DIM + DIM + 1;
        if (toRow(index) % 2 == 0 && isMarkedField(index) && isMarkedField(sq1) && isMarkedField(sq2) && isMarkedField(sq3) && index <= Board.DIM*(Board.DIM+1)*2-1-(DIM*2+1) && index % (DIM+DIM+1) <5) {
            setField(index, m);
            return true;
        }
        return false;
    }


    /**
     * Returns true if the game is over. The game is over when there is a winner
     * or the whole board is full.
     * @return true if the game is over
     */
    //@ ensures isFull() ==> \result == true;
    public boolean gameOver() {
        return isFull();
    }

    /**
     * Check if the game is draw or not.
     * @return True if game is draw; otherwise False
     */
    public boolean isDraw() {
        int wins = 0;
        for (int i = 0; i <= 10; i++){
            if(hasSquare(i,Mark.AA)){
                wins++;
            }
        }
        if (wins==(int)(DIM*DIM/2)){
            return true;
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
        for (int i = 0; i <= 10; i++){
            if(hasSquare(i,m)){
                wins++;
            }
        }
        if (wins>=(int)(DIM*DIM/2)){
            return true;
        }
        return false;
    }


    public boolean hasWinner() {
         return isWinner(Mark.AA) || isWinner(
                 Mark.BB);
    }

    /**
     * Returns a String representation of this board. In addition to the current
     * situation, the String also shows the numbering of the fields.
     *
     * @return the game situation as String
     */
    public String toString() {
        String dot = String.valueOf('\u2022'); // unicode hex

        int indexNumbering = 0;

        String s = ""; // for both left and right board
        for (int i = 0; i < DIM; i++) {
            String row = "";
            for (int j = 0; j < DIM; j++) {
                //                String choice = getField(i, j).toString().substring(0, 1);
                //                switch(choice) {
                //                    case "X":
                //                        row +=  getField(i, j).toString().substring(0, 1)
                //                                .replace("X", "---");
                //                        break;
                //                    case "O":
                //                        row += getField(i, j).toString().substring(0, 1)
                //                                .replace("O", "|");
                //                        break;
                //                    default:
                //                        row += getField(i, j).toString().substring(0, 1)
                //                                .replace("E", "") + dot;
                //                }
                row += " " + getField(i, j).toString().substring(0, 1)
                        .replace("E", " ") + dot;

                if (j < DIM - 1) {
                    row = row + "  "; // separate the dots of the left board
                }

            }

            s = s + row + DELIM; // separate the two boards

            // TODO: Creating the row for horizontal line
            for (int j = 0; j < DIM - 1; j++) {
                String temporaryRowForHorizontal = dot + "    ";
                String indexStr = Integer.toString(indexNumbering);
                temporaryRowForHorizontal = Helper.myReplace(temporaryRowForHorizontal, indexStr, 2);

                s += temporaryRowForHorizontal;

                if (j < DIM - 2) {
                    row = row + "  "; // separate the dots
                }
                indexNumbering++;
            }
            s = s + dot; // last dot on the upper line

            if (i < DIM - 1) { // transition to the vertical line
                s = s + "\n";
                String rowAlign = " " + "    ".repeat(DIM-1) + " ".repeat(DIM) + DELIM; // space for dot + horizontal line + DELIM
                s+= rowAlign; // for separating 2 boards
                //                s+= "1";

                // TODO: Creating the row for vertical line
                for (int k = 0; k < DIM; k++) {
                    String indexStr = Integer.toString(indexNumbering);
                    String temporaryRowForVertical =  "     ";
                    temporaryRowForVertical = Helper.myReplace(temporaryRowForVertical, indexStr, 0);

                    s += temporaryRowForVertical;


                    if (k < DIM - 1) {
                        row = row + " "; // separate the dots
                    }

                    indexNumbering++;
                }

                s += "\n";
            }

        }
        return s;
    }

    /**
     * Empties all fields of this board (i.e., let them refer to the value
     * Mark.EMPTY).
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM*DIM); fields[i] == Mark.EMPTY);
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
    public int toRow(int index) {
        if(index % (DIM * 2 + 1) < DIM) {
            return index - (DIM + (DIM + 1));
        }
        else {
            return index - (DIM * 2 + DIM + 1);
        }
    }

    /**
     * Given an index of a field, convert to the index of the corresponding row.
     * @param index the index of the field
     * @return the corresponding col for that index
     */
    public int toColumn(int index) {
        if(index % (DIM*2+1) <DIM){
            return index-toRow(index)/(DIM+DIM+1);
        }
        else {
            return ((index - toRow(index) - DIM )/ (DIM + DIM + 1))+1;
        }
    }
}
