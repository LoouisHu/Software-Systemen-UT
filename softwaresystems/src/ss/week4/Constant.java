package ss.week4;

public class Constant implements Function, Integrandable {
	
	private double value;
	
	public Constant(double value) {
		this.value = value;
	}

	@Override
	public double apply(double x) {
		return value;
	}

	@Override
	public Function derivative() {
		return new Constant(0);
	}
	
	@Override
	public String toString(){
		return Double.toString(value);
	}

	@Override
	public Function integrand() {
		return new Product(new Constant(value), new Exponent(1));
	}
}
