package ss.week4.tictactoe;

/**
 * Executable class for the game Tic Tac Toe. The game can be played against the
 * computer. Lab assignment Module 2
 * 
 * @author Theo Ruys
 * @version $Revision: 1.4 $
 */
public class TicTacToe {
	public static void main(String[] args) {
		if (args.length == 2){
		Player p1 = new HumanPlayer(args[0], Mark.OO);
		Player p2 = new HumanPlayer(args[1], Mark.XX);
		Game g = new Game(p1, p2);
		g.start();
		}
	}
}
