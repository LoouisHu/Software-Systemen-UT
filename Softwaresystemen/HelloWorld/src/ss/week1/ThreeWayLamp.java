package ss.week1;

public class ThreeWayLamp {
	
	private int status;
	public static final int OFF = 0;
	public static final int LOW = 1;
	public static final int MID = 2;
	public static final int HIGH = 3;
	
	//@ requires status >= 0;
	//@ requires status < 4;
	//@ ensures getStatus() == status;
	
	public ThreeWayLamp(int status){
		this.status = status;
		
	}
		
	public static void main(String[] args){
		ThreeWayLamp lamp = new ThreeWayLamp(3);
		int test = lamp.status;
		System.out.println(test);
		lamp.switchSetting();
		
		System.out.println(lamp.getStatus());
					
						
	}
	//@ensures \result > 0;
	//@ensures \result < 4;
	/*@pure*/public int getStatus(){
		return status;	
	}
	
	public void switchSetting(){
		this.status = (status + 1) % 4;
	}

		
}
	
	
