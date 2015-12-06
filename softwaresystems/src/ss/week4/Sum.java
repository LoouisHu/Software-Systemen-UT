package ss.week4;

public class Sum implements Function, Integrandable {
	
	private Function f;
	private Function g;
	
	public Sum(Function f, Function g) {
		this.f = f;
		this.g = g;
	}

	@Override
	public double apply(double x) {
		return f.apply(x) + g.apply(x);
	}

	@Override
	public Function derivative() {
		return new Sum(f.derivative(), g.derivative());
	}

	@Override
	public String toString(){
		return "(" + f.toString() + " + " + g.toString() + ")";
	}

	@Override
	public Function integrand() {
		if (f instanceof Integrandable && g instanceof Integrandable) {
			return new Sum(((Integrandable) f).integrand(), ((Integrandable) g).integrand());
		}	
		return null;
}
}
