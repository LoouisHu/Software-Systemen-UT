package ss.week4.test;
import ss.week4.Polynomial;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

public class PolynomialTest {

	private Polynomial poly;
	private double[] parts = {3.0, 3.0};
	
	@Before
	public void setUp() throws Exception {
		poly = new Polynomial(parts);
	}

	@Test
	public void test() {
		assertEquals("Check functions returns correctly ", 6.0, poly.apply(1.0), 0.000001);
		System.out.println(poly);
		assertEquals("Check functions #2 returns correctly ", 18.0, poly.apply(2.0), 0.000001);
		assertEquals("Check derivative returns correctly ", 9.0, poly.derivative().apply(1.0), 0.000001);
		assertEquals("Check derivative #2 returns correctly ", 15.0, poly.derivative().apply(2.0), 0.0001);
		assertEquals("Check snd derivative returns correctly ", 6.0, poly.derivative().derivative().apply(1.0), 0.0001);
	}

}
