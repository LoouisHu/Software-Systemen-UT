package week5;

public class ComputerPlayer extends Player {
	private Strategy strategy;
	
	public ComputerPlayer(Mark mark, Strategy strategy) {
		super(strategy.getName() + "-" + mark.toString(), mark);
		this.strategy = strategy;
	}
	
	public ComputerPlayer(Mark mark) {
		this(mark, new NaiveStrategy());
	}

	@Override
	public int determineMove(Board board) {
		return strategy.determineMove(board, this.getMark());
	}

}
