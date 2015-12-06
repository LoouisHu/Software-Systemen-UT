package week2;

public class ThreeWayLampTwo {
	public enum Status {OFF, LOW, MED, HIGH};
	
	private Status status;
	
	
	//@ ensures getStatus() == status;
	
	public ThreeWayLampTwo(Status status){
		this.status = status;
		assert getStatus() == status;
		
	}
		
	
	
	public static void main(String[] args){
	
	}
	

	//@ pure
	/*pure*/ public Status getStatus(){
		return status;
	}
	
	//@ ensures \old(getStatus() == Status.OFF) ==> getStatus() == Status.LOW;
	//@ ensures \old(getStatus() == Status.LOW) ==> getStatus() == Status.MED;
	//@ ensures \old(getStatus() == Status.MED) ==> getStatus() == Status.HIGH;
	//@ ensures \old(getStatus() == Status.HIGH) ==> getStatus() == Status.OFF;
	
	
	public void switchSetting(){
		switch (status) {
		case OFF: 
			status = Status.LOW;
		break;
		case LOW: 
			status = Status.MED;
		break;
		case MED: 
			status = Status.HIGH;
		break;
		case HIGH: 
			status = Status.OFF;
		break;
		default: 
			status = Status.OFF;
		}
	}

}
	

