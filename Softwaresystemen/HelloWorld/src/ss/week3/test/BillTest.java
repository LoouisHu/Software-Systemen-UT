package ss.week3.test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;
import ss.week3.hotel.*;

public class BillTest {

	private Bill bill;
	private Bill nullBill;
	
	@Before
	public void setUp() throws Exception{
		bill = new Bill(null);
	
	}
	
	@Test
	public void beginTest() {
		assertEquals("Initiele waarde moet null zijn", 0.0, bill.getSum(), 0.000001);
	}
	@Test
	public void addItemTest() {
		bill.newItem(new ItemBill(3, "Snoep"));
		assertEquals("Item 1: ", 3.0, bill.getSum(), 0.000001);
		bill.newItem(new ItemBill(1, "Handdoek"));
		assertEquals("Item 1, 2: ", 4.0, bill.getSum(), 0.000001);
	}
}
