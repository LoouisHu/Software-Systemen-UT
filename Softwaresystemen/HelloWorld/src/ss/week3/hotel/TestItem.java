package ss.week3.hotel;

import ss.week3.hotel.Bill.Item;

public class TestItem implements Bill.Item{
	public double amount = 1.00;
	public String  description = "Foobar: ";

	@Override
	public double getAmount() {
		return amount;
	}

	@Override
	public String getDescription() {
		return description;
	}

	@Override
	public void add(Item item) {
		
	}

}
