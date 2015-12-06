package week3.test;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;
import week3.hotel.*;



public class BillTest {
	private Bill bill;
	
	@Before
	public void setUp() throws Exception{
		bill = new Bill(null);
	}
	
	@Test
	public void beginTest() {    
	      assertEquals("Startsum is zero", 0.0, bill.getSum(), 0.000001 );
	}
	     
	
	@Test
	public void newItemTest(){
		bill.newItem(new BillItem(1.0, "snoep"));
		assertEquals("Add item one", 1.0, bill.getSum(), 0.000001);
		bill.newItem(new BillItem(2.0, "lolly"));
		assertEquals("Add item two", 2.0, bill.getSum(), 0.000001);
		bill.newItem(new BillItem(5.0, "gehaktbal"));
		assertEquals("Add item five", 5.0, bill.getSum(), 0.000001);
		
	}
}