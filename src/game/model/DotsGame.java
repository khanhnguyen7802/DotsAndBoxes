package game.model;

import java.util.ArrayList;
import java.util.List;

/**
 * Represent a TicTacToe game: keep track of whom the players and whose turn it is.
 */
public class DotsGame implements Game {
    private Board board;
    public Player player1;
    public Player player2;
    public int turnIndex;


    /**
     * Constructor that creates an instance of TicTacToe game.
     * @param player1 - 1st player of the game with Mark.XX;
     * @param player2 - 2nd player of the game with Mark.OO;
     */
    public DotsGame(AbstractPlayer player1, AbstractPlayer player2) {
        this.board = new Board();
        this.player1 = player1;
        this.player2 = player2;
        turnIndex = 0; // player X starts first
    }


    /**
     * Returns a String representing the current
     * state of the game, i.e., the board and whose turn it is
     *
     * @return the formatted String
     */
    public String toString() {
        return this.board + " - Player turn: " + getTurn();
    }

    /**
     * Get board of the current game.
     * @return this.board;
     */
    //@pure;
    public Board getBoard() {
        return this.board;
    }


    /**
     * Check if the game is over.
     * @return board.gameOver();
     */
    //@pure;
    @Override
    public boolean isGameover() {
        return board.isGameOver();
    }

    /**
     * Get the player whose turn it is.
     * @return the player that is having his turn
     */
    //@pure;
    @Override
    public Player getTurn() {
        if (turnIndex == 0)
            return player1;
        else
            return player2;
    }

    /**
     * Return the winner, if there is one.
     * @return player1 || player2 || null;
     */
    //@pure;
    @Override
    public Player getWinner() {
        if (board.hasWinner()) {
            if (board.isWinner(Mark.AA))
                return player1;
            else return player2;
        }
        return null;
    }

    /**
     * Switch the turn index (i.e., give turn to the other player).
     */
    public void switchTurnIndex() {
        if(this.turnIndex == 0)
            this.turnIndex = 1;
        else
            this.turnIndex = 0;
    }
    /**
     * Return the list containing all the valid moves.
     * @return a list of valid moves
     */
    //@pure;
    @Override
    public List<Move> getValidMoves() { // considering all empty moves
        List<Move> moves = new ArrayList<>();
        Mark currentMark = turnIndex == 0 ? Mark.AA : Mark.BB;
        for (int i = 0; i < board.DIM*2; i++)
            if(i % 2 == 0) {
                for (int j = 0; j < board.DIM; j++) {
                    Move currentMove = new DotsMove(i, j, currentMark);
                    if (board.isEmptyField(i, j)) moves.add(currentMove);
                }
            }else {
                for (int j = 0; j <= board.DIM; j++) {
                Move currentMove = new DotsMove(i, j, currentMark);
                if (board.isEmptyField(i, j)) moves.add(currentMove);
                }
            }
        return moves;
    }

    /**
     * Check if the move is valid.
     * @param move - the move to check
     * @return True if the move is valid; otherwise False
     */
    @Override
    public boolean isValidMove(Move move) {
        if (!(move instanceof DotsMove)) {
            return false;
        }
        DotsMove dotsMove = (DotsMove) move;
        return board.isEmptyField(dotsMove.getRow(), dotsMove.getCol()) && board.isField(
                dotsMove.getRow(), dotsMove.getCol());
    }

    /**
     * Do a move in the game of TicTacToe.
     * @param move the move to play
     */
    //@ensures board != null && isValidMove(move);
    @Override
    public void doMove(Move move) {
        DotsMove tm = (DotsMove) move;
        if(isValidMove(move)) {
            if (getTurn() == player1) {
                board.setField(tm.getRow(), tm.getCol(), Mark.FILLED);
                this.turnIndex = 1;
                for (int i = 0; i< Board.DIM * (Board.DIM + 1) * 2;i++){
                    if(board.hasSquare(i,Mark.FILLED)){
                        board.setField(i,Mark.AA);
                        this.turnIndex = 0;
                    }
                }
            }
            else {
                board.setField(tm.getRow(), tm.getCol(), Mark.FILLED);
                this.turnIndex = 0;
                for (int i = 0; i< Board.DIM * (Board.DIM + 1) * 2;i++){
                    if(board.hasSquare(i,Mark.FILLED)){
                        board.setField(i,Mark.BB);
                        this.turnIndex = 1;
                    }
                }
            }
        }
    }

    @Override
    public void resetBoard(Board board) {
        this.board = board;
    }

}
