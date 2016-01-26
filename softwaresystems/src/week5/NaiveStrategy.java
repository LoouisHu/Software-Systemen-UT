package week5;

import java.util.Random;

public class NaiveStrategy implements Strategy {

	private final static String NAME = "Naive";
	private static Random random = new Random();
	
	public NaiveStrategy() {
		// TODO Auto-generated constructor stub
	}

	@Override
	public String getName() {
		// TODO Auto-generated method stub
		return NaiveStrategy.NAME;
	}

	@Override
	public int determineMove(Board b, Mark m) {
		// TODO Auto-generated method stub
		int res;
		while (!b.isEmptyField(res = random.nextInt((Board.DIM*Board.DIM)-1)));
		return res;
	}

}
