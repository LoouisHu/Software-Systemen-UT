package ss.week3.hotel;

import ss.week3.hotel.Bill.Item;

public class ItemBill implements Bill.Item{
	public double amount;
	public String  description;
	
	public ItemBill(double amount, String description){
		this.amount = amount;
		this.description = description;
	}
	
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
	
	public String toString(){
		return description;
	}

}
