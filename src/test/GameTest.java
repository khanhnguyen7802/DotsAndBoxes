package test;

import game.model.*;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static game.model.Board.DIM;
import static org.junit.jupiter.api.Assertions.*;

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
     * This method checks wether doMove does a Move correctly
     */
    @Test
    public void testMove(){
        Move determinedMove = new DotsMove(0, 0, Mark.AA);
        game.doMove(determinedMove);
        assertTrue(Mark.FILLED == game.getBoard().getField(0));
    }

    /**
     * This test checks wether a box is filled in when the conditions
     * are met.
     */
    @Test
    public void testBox(){
        game.turnIndex = 1;
        Move move1 = new DotsMove(0, 0, Mark.AA);
        game.doMove(move1);
        Move move2 = new DotsMove(2, 0, Mark.AA);
        game.doMove(move2);
        Move move3 = new DotsMove(1, 0, Mark.AA);
        game.doMove(move3);
        Move move4 = new DotsMove(1, 1, Mark.AA);
        game.doMove(move4);
        assertTrue(game.getBoard().getField(0) == Mark.AA);
    }

    /**
     * This test checks if it is possible to whin and that the
     * winning player is returned correctly.
     */
    @Test
    public void testWinningCondition(){
        for (int i = 0; i < Board.DIM * (Board.DIM + 1) * 2; i++) {
            int row = board.toRow(i);
            int col = board.toColumn(i);
            Move move = new DotsMove(row, col, Mark.AA);
            game.doMove(move);
            if (game.isGameover()){
                assertTrue(game.getWinner() == player2);
            }
        }
    }

    /**
     * This test checks wether or not is it possible to play
     * a full game, and do we always get a winner
     */
    @Test
    public void testRandom(){
        List<Move> possibleMoves = game.getValidMoves();
        while ((possibleMoves.size()-1 >0)){
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
    }
}


