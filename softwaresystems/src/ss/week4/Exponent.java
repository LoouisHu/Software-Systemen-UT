package ss.week4;

public class Exponent implements Function, Integrandable {

	private int exponent;
	
	public Exponent(int exponent) {
		this.exponent = exponent;
	}

	@Override
	public double apply(double x) {
		return Math.pow(x, exponent);
	}

	@Override
	public Function derivative() {
		if (exponent > 0) {
			return new LinearProduct(new Exponent(exponent - 1), new Constant(exponent));
		}
		return new Constant(exponent);
	}
	
	public String toString(){
		return "(x^" + exponent + ")";
	}

	@Override
	public Function integrand() {
		return new Product(new Constant(1/(exponent+1)), new Exponent(exponent + 1));
	}
	
}
