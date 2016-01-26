package week5;

/**
 * Executable class for the game Tic Tac Toe. The game can be played against the
 * computer. Lab assignment Module 2
 * 
 * @author Theo Ruys
 * @version $Revision: 1.4 $
 */
public class TicTacToe {
	
	public static Player determinePlayer(String arg, Mark mark){
		String argu = arg;
		if(argu.equals("-N")){
			return new ComputerPlayer(mark, new NaiveStrategy());
		} else if (argu.equals("-S")){
			return new ComputerPlayer(mark, new SmartStrategy());
		} else {
			return new HumanPlayer(arg, mark);
		}
	}
	
	public static void main(String[] args) {
		if (args.length == 2){
		Player p1 = determinePlayer(args[0], Mark.XX);
		Player p2 = determinePlayer(args[1], Mark.OO);
		Game g = new Game(p1, p2);
		g.start();
		}else {
			System.out.println("Error! Args length != 2!");
		}
	}

}
	