package week3;

public class Multiplication implements OperatorWithIdentity {

	@Override
	public int operate(int left, int right) {
		// TODO Auto-generated method stub
		return left+right;
	}

	@Override
	public int identity() {
		// TODO Auto-generated method stub
		return 1;
	}

}
