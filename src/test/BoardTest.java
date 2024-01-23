package test;

import game.model.Board;
import game.model.Mark;
import java.util.Arrays;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static game.model.Board.DIM;
import static org.junit.jupiter.api.Assertions.*;

/**
 * Testing the board.
 */
public class BoardTest {
    private Board board;

    @BeforeEach
    public void setUp() {
        board = new Board();
    }

    /**
     * Test if the board is initialized with all empty fields.
     */
    @Test
    public void testBoard() {
        int numberOfLines = Board.DIM * (Board.DIM + 1) * 2 - 1;
        for (int i = 0; i <= numberOfLines; i++) {
            assertEquals(Mark.EMPTY, board.getField(i));
        }

    }

    /**
     * Test deepCopy() method.
     * Check if it indeed creates another exact copy of the original board.
     */
    @Test
    public void testDeepCopy() {
        board.setField(0, Mark.AA);
        board.setField(1, Mark.BB);
        Board deepCopyBoard = board.deepCopy();

        // First test if all the fields are the same
        for (int i = 0; i < Board.DIM * (Board.DIM + 1) * 2 - 1; i++) {
            assertEquals(board.getField(i), deepCopyBoard.getField(i));
        }

    }

    /**
     * Test the index() method.
     * Check if the method returns the right index of the field, given the index of row and col
     */
    @Test
    public void testIndex() {
        // check the index method with various row and column values
        assertEquals(0, board.index(0, 0));
        assertEquals(10, board.index(1, 5));
        assertEquals(30, board.index(5, 3));
        assertEquals(59, board.index(10, 4));
    }

    /**
     * Test isField(int index) method.
     * Check if a random index is a valid index of a field on the board.
     */
    @Test
    public void testIsFieldIndex() {
        assertFalse(board.isField(-1));
        assertFalse(board.isField(60));

        assertTrue(board.isField(0));
        assertTrue(board.isField(59));

    }


    /**
     * Test isField(int row, int col) method.
     * Given a row and col, check if it is a valid field.
     */
    @Test
    public void testIsFieldRowCol() {
        assertFalse(board.isField(-1, 0));
        assertFalse(board.isField(0, -1));
        assertFalse(board.isField(11, 0));
        assertFalse(board.isField(0, 6));

        assertTrue(board.isField(0, 0));
        assertTrue(board.isField(2, 2));
        assertFalse(board.isField(10, 5));
        assertFalse(board.isField(10, 6));
    }


    /**
     * Test setField(int index) and getField(int index) method.
     * Check if we can set the field and get the field (given the index).
     */
    @Test
    public void testSetAndGetFieldIndex() {
        assertEquals(Mark.EMPTY, board.getField(0));

        board.setField(0, Mark.FILLED);
        assertEquals(Mark.FILLED, board.getField(0));

        board.setField(1, Mark.AA);
        assertEquals(Mark.AA, board.getField(1));

        board.setField(2, Mark.BB);
        assertEquals(Mark.BB, board.getField(2));
    }

    /**
     * Test setField(int row, int col) and getField(int row, int col) method.
     * Check if we can set the field and get the field (given the row and the col).
     */
    @Test
    public void testGetFieldRowAndCol() {
        assertEquals(Mark.EMPTY, board.getField(0, 0));

        board.setField(0, 0, Mark.FILLED);
        assertEquals(Mark.FILLED, board.getField(0, 0));

        board.setField(1, 1, Mark.AA);
        assertEquals(Mark.AA, board.getField(1, 1));

        board.setField(2, 2, Mark.BB);
        assertEquals(Mark.BB, board.getField(2, 2));
    }

    /**
     * Test isEmptyField(int index) method.
     * Check if the field is empty (given the index).
     */
    @Test
    public void testIsEmptyFieldIndex(){
        assertTrue(board.isEmptyField(0));

        board.setField(0, Mark.FILLED);
        assertFalse(board.isEmptyField(0));
    }

    /**
     * Test isEmptyField(int row, int col) method.
     * Check if the field is empty (given the row, col).
     */
    @Test
    public void testIsEmptyFieldRowAndCol(){
        assertTrue(board.isEmptyField(0,0));

        board.setField(0,0, Mark.FILLED);
        assertFalse(board.isEmptyField(0,0));
    }

    /**
     * Test isMarkedField(int index) method.
     * Check if at a given index, the field is marked as FILLED or not.
     */
    @Test
    public void testIsMarkedField() {
        assertFalse(board.isMarkedField(0));

        board.setField(0, Mark.FILLED);
        assertTrue(board.isMarkedField(0));

    }

    /**
     * Test isFull() method.
     * Check if the board is full or not.
     */
    @Test
    public void testIsFull() {
        assertFalse(board.isFull());

        for (int i = 0; i < Board.DIM * (Board.DIM + 1) * 2; i++) {
            board.setField(i, Mark.FILLED);
        }
        assertTrue(board.isFull());
    }

    /**
     * Test hasSquare() method.
     * Check if the player is able to form a square at that index
     */
    @Test
    public void testHasSquare() {
        assertFalse(board.hasSquare(0, Mark.FILLED));

        board.setField(0, Mark.FILLED);
        board.setField(5, Mark.FILLED);
        board.setField(6, Mark.FILLED);
        board.setField(11, Mark.FILLED);

        assertTrue(board.hasSquare(0, Mark.FILLED));

        board.setField(0, Mark.AA);
        assertTrue(board.getField(0) == Mark.AA);
    }

    /**
     * Test gameOver() method.
     * Check if the game is over or not.
     */
    @Test
    public void testIsGameOver() {
        assertFalse(board.isGameOver());

        for (int i = 0; i < Board.DIM * (Board.DIM + 1) * 2; i++) {
            board.setField(i, Mark.AA);
        }
        assertTrue(board.isGameOver());

    }

    /**
     * Test isDraw() method.
     * Check if the board returns the draw case.
     */
    @Test
    public void testIsDraw() {
        // TODO
    }

    /**
     * Test isWinner() method.
     * Check if the player with a given mark is the winner.
     */
    @Test
    public void testIsWinner() {
        // TODO

    }

    /**
     * Test hasWinner() method.
     * Check if there is a winner on the board.
     */
    @Test
    public void testHasWinner() {
        // TODO

    }

    /**
     * Test reset() method.
     * Check if the board resets to all Mark.EMPTY
     */
    @Test
    public void testReset() {
        board.setField(0, 0, Mark.AA);
        board.setField(1, 1, Mark.BB);
        board.reset();
        assertEquals(Mark.EMPTY, board.getField(0, 0));
        assertEquals(Mark.EMPTY, board.getField(1, 1));
    }

    /**
     * Test toRow() method.
     * Check if it can convert to a row index (given a field index)
     */
    @Test
    public void testToRow() {
        assertEquals(0, board.toRow(0));
        assertEquals(0, board.toRow(4));
        assertEquals(10, board.toRow(59));
        assertEquals(7, board.toRow(42));
    }

    /**
     * Test toCol() method.
     * Check if it can convert to a column index (given a field index)
     */
    @Test
    public void testCol() {
        assertEquals(0, board.toColumn(0));
        assertEquals(4, board.toColumn(37));
        assertEquals(5, board.toColumn(43));
        assertEquals(0, board.toColumn(5));
    }

//        @Test
//        public void testCheckMove() {
//            // Test the checkMove method with various move values
//            /**
//             *   0  1  2  3  4  5  6  7
//             * 0
//             *  --+--+--+--+--+--+--+--
//             * 1
//             *  --+--+--+--+--+--+--+--
//             * 2
//             *  --+--+--+--+--+--+--+--
//             * 3         o  x
//             *  --+--+--+--+--+--+--+--
//             * 4         x  o
//             *  --+--+--+--+--+--+--+--
//             * 5
//             *  --+--+--+--+--+--+--+--
//             * 6
//             *  --+--+--+--+--+--+--+--
//             * 7
//             *  --+--+--+--+--+--+--+--
//             */
//            // for example the first move (row 4, col 5, Mark XX),
//            // which is valid and after which 1 opponent's disc will be flipped
//            assertTrue(board.checkMove(4,5,Mark.XX));
//            assertEquals(1, Board.flippedDiscs.size());
//            // second move is (row 0, col 0, Mark OO),
//            // which is not valid and after which 0 opponent's disc will be flipped
//            assertFalse(board.checkMove(0,0,Mark.OO));
//            assertEquals(0, Board.flippedDiscs.size());
//        }
//
//        @Test
//        public void getWinnerMark() {
//            //fill all fields with dark marks
//            //the winner should be XX
//            Arrays.fill(board.fields, Mark.XX);
//            assertEquals(Mark.XX, board.getWinnerMark());
//
//            //fill 2 fields with OO marks and 1 field with XX mark
//            //the winner should be OO
//            Arrays.fill(board.fields, Mark.EMPTY);
//            board.setField(0,1,Mark.OO);
//            board.setField(0,2,Mark.OO);
//            board.setField(0,3,Mark.XX);
//            assertEquals(Mark.OO, board.getWinnerMark());
//
//            //Equal number of marks on the board
//            //should return empty mark
//            Arrays.fill(board.fields, Mark.EMPTY);
//            board.setField(0,1,Mark.OO);
//            board.setField(0,2,Mark.XX);
//            assertEquals(Mark.EMPTY, board.getWinnerMark());
//        }
//    }
}
