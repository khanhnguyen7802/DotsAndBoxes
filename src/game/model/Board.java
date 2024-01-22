package game.model;

/**
 * Board for the Tic Tac Toe game.
 */

public class Board {
    /**
     * Dimension of the board, i.e., if set to 5, the board has 5 rows and 5-6 columns.
     */
    public static final int DIM = 6;
    private static final String DELIM = "     ";
    private static final String[] NUMBERING = {
            //TODO
    };
    private static final String LINE = NUMBERING[1];

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
    this.fields = new  Mark[Board.DIM*Board.DIM*2];
    for (int i = 0; i<Board.DIM*Board.DIM*2; i++) {
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
        for (int i = 0; i >= 0 && i<Board.DIM*Board.DIM*2; i++){
            newBoard.fields[i] = this.fields[i];
        }

        return newBoard;
    }

    /**
     * //TODO.
     */
    public int index(int row, int col) {
        int indexes = 0;
        if(row % 2 == 0){
            return (DIM + DIM + 1)*row/2 + col;
        }
        else{
            return (row*DIM)+col+(row-1)/2;
        }
    }




    public boolean isField(int index) {
        return index >= 0 && index < Board.DIM*Board.DIM*2;
    }
    public boolean isField(int row, int col) {
        if(row % 2 == 0){
            return row >= 0 && col >= 0 && row<=DIM*2 && col<=DIM-1;
        }
        else {
            return row >= 0 && col >= 0 && row < DIM * 2 && col <= DIM;
        }
    }

    /**
     * Returns the content of the field i.
     * @param i the number of the field (see NUMBERING)
     * @return the mark on the field
     */
    /*@ requires isField(i);
    ensures \result == Mark.EMPTY || \result == Mark.BB || \result == Mark.AA;
     @*/
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
    ensures \result == Mark.EMPTY || \result == Mark.BB || \result == Mark.AA;
     @*/
    public Mark getField(int row, int col) {
        int indexConvert = index(row, col);

        return getField(indexConvert);
    }

    /**
     * Returns true if the field i is empty.
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
     * @return true if the field is empty
     */
    /*@ requires isField(row, col);
    ensures getField(row, col) == Mark.EMPTY ==> \result == true;
     @*/
    public boolean isEmptyField(int row, int col) {
        int indexConvert = index(row, col);
        return getField(indexConvert) == Mark.EMPTY;
    }

    /**
     * Tests if the whole board is full.
     * @return true if all fields are occupied
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM*DIM); fields[i] == Mark.AA || fields[i] == Mark.BB);
    public boolean isFull() {
    	 for (int i = 0; i < Board.DIM*Board.DIM*2; i++){
             if (isEmptyField(i))
                 return false;
         }
         return true;
    }

    public boolean hasSquare(){

        return false;
    }


    /**
     * Returns true if the game is over. The game is over when there is a winner
     * or the whole board is full.
     * @return true if the game is over
     */
    //@ ensures isFull() || hasWinner() ==> \result == true;
    public boolean gameOver() {
        return isFull() ;
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
        //TODO
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
        //TODO
        return null;
    }

    /**
     * Empties all fields of this board (i.e., let them refer to the value
     * Mark.EMPTY).
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM*DIM); fields[i] == Mark.EMPTY);
    public void reset() {
        for(int i = 0; i< Board.DIM*Board.DIM*2;i++){
            setField(i, Mark.EMPTY);
        }
    }

    /**
     * Sets the content of field i to the mark m.
     * @param i the field number (see NUMBERING)
     * @param m the mark to be placed
     */
    /*@ requires isField(i);
    ensures getField(i) == m;
     @*/
    public void setField(int i) {
        if(isField(i)){
            fields[i] = Mark.FILLED;
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
    public void setField(int row, int col) {
        fields[index(row,col)] = Mark.FILLED;
    }

    /**
     *
     * @param index
     * @return
     */
    public int toRow(int index) {
        if(index % 2 == 0){
            return 0;
        }
        else {
            return 0;
        }
    }

    public int toColumn(int index) {
        if(index % 2 == 0){
            return 0;
        }
        else {
            return 0;
        }
    }
}
