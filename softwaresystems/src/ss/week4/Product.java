package ss.week4;

public class Product implements Function {

	protected Function f;
	protected Function g;
	
	public Product(Function f, Function g) {
		this.f = f;
		this.g = g;
	}

	@Override
	public double apply(double x) {
		return f.apply(x) * g.apply(x);
	}

	@Override
	public Function derivative() {
		
		return new Sum(new Product(f.derivative(), g), new Product(g.derivative(), f));
	}
	
	@Override
	public String toString(){
		return "(" + g.toString() + " * " + f.toString() + ")";
	}

}
