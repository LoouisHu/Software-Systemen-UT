package ss.week4;

public class LinearProduct extends Product implements Integrandable {

	public LinearProduct(Function f, Constant g) {
		super(g, f);
		
	}

	@Override
	public Function integrand() {
		if (g instanceof Integrandable && f instanceof Constant) {
			return new LinearProduct(((Integrandable) g).integrand(), (Constant) f);
	}
		return null;
	}
	
	@Override
	public Function derivative(){
		return new LinearProduct(g.derivative(), (Constant) f );
	}
}
