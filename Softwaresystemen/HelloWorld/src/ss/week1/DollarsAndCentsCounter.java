package ss.week1;

public class DollarsAndCentsCounter {
	public int cents;

	public int dollars(){
		return cents/100;
	}
	
	public int cents(){
		return  cents % 100;
	}
	
	public void add (int dollars, int cents){
		this.cents = this.cents + 100 * dollars + cents;
		
	}

	public void reset (){
			this.cents = 0;
	}
		
	public void subtract (int dollars, int cents){
			this.cents = this.cents - 100 * dollars - cents;
	
	}
}
