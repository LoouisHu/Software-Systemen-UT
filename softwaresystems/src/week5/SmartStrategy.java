package week5;

import java.util.Random;

public class SmartStrategy implements Strategy {

	private final static String NAME = "Smart";
	private static Random random = new Random();
	@Override
	public String getName() {
		// TODO Auto-generated method stub
		return SmartStrategy.NAME;
	}

	@Override
	public int determineMove(Board b, Mark m) {
		// TODO Auto-generated method stub
		int row, col;
		if (b.isEmptyField(row = Math.floorDiv(Board.DIM, 2), col = Math.floorDiv(Board.DIM, 2))){
			return b.index(row, col);
		}
		
		for (int i = 0 ; i < (Board.DIM*Board.DIM); i++){
			Board board = b.deepCopy();
			board.setField(i, m);
			if (board.isWinner(m)){
				return i;
			}
		}
		return doRandomMove(b);
			
	}
	
	public int doRandomMove(Board b){
		int res;
		while (!b.isEmptyField(res = random.nextInt(Board.DIM*Board.DIM)));
		return res;
	}

}
