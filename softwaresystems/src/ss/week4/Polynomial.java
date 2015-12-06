package ss.week4;

public class Polynomial implements Function, Integrandable {

	private LinearProduct[] polya;
	private double[] values;
	
	public Polynomial(double[] values) {
		this.values = values;
		polya = new LinearProduct[values.length];
		
		for (int i = 0; i < polya.length; i++){
		polya[i] =	new LinearProduct( new Exponent(i),new Constant(values[i]));
		}
	}
	
	@Override
	public Function integrand() {
		double[] g = new double[polya.length + 1];
		for (int i = 0; i < polya.length; i++){
			new Product(new Constant(i), new Exponent(i+1));
		}
		g[0]=0;
		return new Polynomial(g);
		
	}

	@Override
	public double apply(double x) {
		double result = 0;
		for (int i = 0; i < polya.length; i++){
			result += polya[i].apply(x);
		}
		return result;
	}

	@Override
	public Function derivative(){
		Function piet = new Constant(0);
		for ( int i = 1; i < values.length; i++){
			piet = new Sum(new LinearProduct( new Exponent(i-1),new Constant(values[i])), piet );
		}
		return piet;
	}
	
	public String toString(){
		return null;
	}

}
