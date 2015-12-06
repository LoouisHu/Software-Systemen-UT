package ss.week3.hotel;
import java.io.PrintStream;
import java.util.ArrayList;

public class Bill {
	public int sum;
	public interface Item {
		public double getAmount();
		String getDescription();
	}

	private ArrayList<Item> items = new ArrayList<Item>();
	private PrintStream output;
	
	public Bill(PrintStream outstream) {
		output = outstream;
		sum = 0;
	}
	
	public void newItem(ItemBill item){
		if (item != null){
			items.add(item);
		if	(output != null){
			output.println(String.format("%-3.30s  %-30.30s%n", "Item: $", item.getAmount()));
		}
			sum += item.getAmount();
		}
	}
	
	public double getSum() {
		return sum;
	}
	
	public void close() {
		if (output != null) {
			
			output.println("Bill cost: $" + getSum());
		}
	}

}
