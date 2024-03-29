package test;

import game.model.*;
import java.util.List;
import java.util.Random;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static game.model.Board.DIM;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Testing the gameLogic.
 */
public class GameTest {
    private Board board;
    private DotsGame game;
    private DotsMove move;
    private AbstractPlayer player1;
    private AbstractPlayer player2;

    @BeforeEach
    public void setUp() {
        board = new Board();
        player1 = new HumanPlayer("pl1", Mark.AA);
        player2 = new HumanPlayer("pl2", Mark.BB);
        game = new DotsGame(player1, player2);
        game.turnIndex = 0;
    }

    /**
     * Test doMove() method.
     * It checks whether doMove indeed does a Move correctly.
     */
    @Test
    public void testDoMove() {
        Move determinedMove = new DotsMove(0, 0, Mark.AA);
        game.doMove(determinedMove);
        assertTrue(Mark.FILLED == game.getBoard().getField(0));
    }

    /**
     * This test checks whether a box is filled in when the conditions
     * are met.
     */
    @Test
    public void testBox() {
        game.turnIndex = 1;
        Move move1 = new DotsMove(0, 0, Mark.FILLED);
        game.doMove(move1);
        Move move2 = new DotsMove(2, 0, Mark.FILLED);
        game.doMove(move2);
        Move move3 = new DotsMove(1, 0, Mark.FILLED);
        game.doMove(move3);
        Move move4 = new DotsMove(1, 1, Mark.FILLED);
        game.doMove(move4);
        assertTrue(game.getBoard().getField(0) == Mark.AA);
    }

    /**
     * Test isGameover() method.
     * Check if the game is over when the board is full.
     */
    @Test
    public void testGameOverCondition() {
        for (int i = 0; i < Board.DIM * (Board.DIM + 1) * 2; i++) {
            int row = board.toRow(i);
            int col = board.toColumn(i);
            Move move = new DotsMove(row, col, Mark.AA);
            game.doMove(move);

            if (i == 59) { // last index
                assertTrue(game.isGameover());
            } else {
                assertFalse(game.isGameover());
            }
        }
    }

    /**
     * This test checks if it is possible to win and that the
     * winning player is returned correctly.
     */
    @Test
    public void testWinningCondition() {
        for (int i = 0; i < Board.DIM * (Board.DIM + 1) * 2; i++) {
            int row = board.toRow(i);
            int col = board.toColumn(i);
            Move move = new DotsMove(row, col, Mark.BB);
            game.doMove(move);
            if (game.isGameover()) {
                assertTrue(game.getWinner() == player2);
            }
        }
    }

    /**
     * This test checks whether it is possible to play
     * a full game, and do we always get a winner.
     * It also checks if every box is filled with either
     * Mark.AA or Mark.BB.
     */
    @Test
    public void testRandom(){
        List<Move> possibleMoves = game.getValidMoves();
        while (possibleMoves.size() - 1 > 0) {
            possibleMoves = game.getValidMoves();
            Random rand = new Random();
            int index = rand.nextInt(possibleMoves.size());
            Move randomMove = possibleMoves.get(index);
            Move move = randomMove;
            game.doMove(move);
        }
        System.out.println("The winner is: " + game.getWinner());
        assertTrue(game.isGameover());
        assertTrue(game.getWinner() != null);
        for (int i = 0; i < Board.DIM * (Board.DIM + 1) * 2 - DIM; i++) {
            if (i % (DIM * 2 + 1) == 0) {
                assertFalse(game.getBoard().getField(i) == Mark.FILLED);
                assertFalse(game.getBoard().getField(i) == Mark.EMPTY);
            }
        }
    }
}


