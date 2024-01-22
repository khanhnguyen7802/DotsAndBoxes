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
            int endIndex = (DIM + (DIM-1))*(DIM-1) + (DIM-1);
            for (int i = 0; i < endIndex; i++) {
                assertEquals(Mark.EMPTY, board.getField(i));
            }

    }


    /**
     * Test if a random index is a valid index of a field on the board.
     */
    @Test
    public void testIsFieldIndex() {
            assertFalse(board.isField(-1));
            assertFalse(board.isField(60));

            assertTrue(board.isField(0));
            assertTrue(board.isField(59));

        }

    /**
     * Test if
     */
    @Test
    public void testIsFieldRowCol() {
        // checks if row and col are valid on a field of the board
        assertFalse(board.isField(-1, 0));
        assertFalse(board.isField(0, -1));
        assertTrue(board.isField(0, 0));
        assertTrue(board.isField(2, 2));
        assertTrue(board.isField(7, 2));
        assertFalse(board.isField(3, 9));
    }

        @Test
        public void testSetAndGetFieldRowCol() {
            board.setField(5, 5, Mark.XX);
            assertEquals(Mark.XX, board.getField(5, 5));
            assertEquals(Mark.EMPTY, board.getField(0, 1));
            assertEquals(Mark.EMPTY, board.getField(1, 0));
            board.setField(1,1,Mark.OO);
            assertEquals(Mark.OO, board.getField(1, 1));
        }

        @Test
        public void testIsEmptyField(){
            board.setField(0,0,Mark.XX);
            assertFalse(board.isEmptyField(0,0));
            board.setField(0,0,Mark.EMPTY);
            assertTrue(board.isEmptyField(0,0));
        }

        @Test
        public void testIsFull() {
            //test if the whole board is full
            board.setField(0,1,Mark.XX);
            assertFalse(board.isFull());

            Arrays.fill(board.fields, Mark.XX);
            assertTrue(board.isFull());
        }

        @Test
        public void testGetFieldIndex() {
            board.setField(0, 1, Mark.XX);
            assertEquals(Mark.XX, board.getField(1));

            //check the default centre
            assertEquals(Mark.OO, board.getField(27));
            assertEquals(Mark.OO, board.getField(36));
        }

        @Test
        public void testReset() {
            //after resetting all fields should be empty
            board.setField(1,1,Mark.XX);
            board.setField(2,4,Mark.OO);
            board.reset();
            assertEquals(Mark.EMPTY, board.getField(1,1));
            assertEquals(Mark.EMPTY, board.getField(2,4));
        }

        @Test
        public void testDeepCopy() {
            board.setField(0, 3,Mark.XX);
            board.setField(5, 2,Mark.OO);
            Board deepCopyBoard = board.deepCopy();

            // First test if all the fields are the same
            for (int i = 0; i < DIM * DIM; i++) {
                assertEquals(board.getField(i), deepCopyBoard.getField(i));
            }

            // check the fields in the copy are equals to the fields in the original
            assertArrayEquals(board.fields, deepCopyBoard.fields);
        }

        @Test
        public void testIndex() {
            // check the index method with various row and column values
            assertEquals(0, board.index(0, 0));
            assertEquals(7, board.index(0, 7));
            assertEquals(8, board.index(1, 0));
            assertEquals(15, board.index(1, 7));
        }

        @Test
        public void testRow() {
            // check the row method with various index values
            assertEquals(0, board.row(0));
            assertEquals(0, board.row(7));
            assertEquals(1, board.row(8));
            assertEquals(1, board.row(15));
        }

        @Test
        public void testCol() {
            // check the col method with various index values
            assertEquals(0, board.col(0));
            assertEquals(7, board.col(7));
            assertEquals(0, board.col(8));
            assertEquals(7, board.col(15));
        }

        @Test
        public void testCheckMove() {
            // Test the checkMove method with various move values
            /**
             *   0  1  2  3  4  5  6  7
             * 0
             *  --+--+--+--+--+--+--+--
             * 1
             *  --+--+--+--+--+--+--+--
             * 2
             *  --+--+--+--+--+--+--+--
             * 3         o  x
             *  --+--+--+--+--+--+--+--
             * 4         x  o
             *  --+--+--+--+--+--+--+--
             * 5
             *  --+--+--+--+--+--+--+--
             * 6
             *  --+--+--+--+--+--+--+--
             * 7
             *  --+--+--+--+--+--+--+--
             */
            // for example the first move (row 4, col 5, Mark XX),
            // which is valid and after which 1 opponent's disc will be flipped
            assertTrue(board.checkMove(4,5,Mark.XX));
            assertEquals(1, Board.flippedDiscs.size());
            // second move is (row 0, col 0, Mark OO),
            // which is not valid and after which 0 opponent's disc will be flipped
            assertFalse(board.checkMove(0,0,Mark.OO));
            assertEquals(0, Board.flippedDiscs.size());
        }

        @Test
        public void getWinnerMark() {
            //fill all fields with dark marks
            //the winner should be XX
            Arrays.fill(board.fields, Mark.XX);
            assertEquals(Mark.XX, board.getWinnerMark());

            //fill 2 fields with OO marks and 1 field with XX mark
            //the winner should be OO
            Arrays.fill(board.fields, Mark.EMPTY);
            board.setField(0,1,Mark.OO);
            board.setField(0,2,Mark.OO);
            board.setField(0,3,Mark.XX);
            assertEquals(Mark.OO, board.getWinnerMark());

            //Equal number of marks on the board
            //should return empty mark
            Arrays.fill(board.fields, Mark.EMPTY);
            board.setField(0,1,Mark.OO);
            board.setField(0,2,Mark.XX);
            assertEquals(Mark.EMPTY, board.getWinnerMark());
        }
    }
}
