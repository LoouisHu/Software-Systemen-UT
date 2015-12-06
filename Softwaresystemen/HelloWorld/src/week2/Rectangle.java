package week2;

public class Rectangle {
	
	private int length;
	private int width;
	
	//@ private invariant this.length > 0;
	//@ private invariant this.width > 0;
	
	//@ requires length > 0;
	//@ requires width > 0;
	//@ ensures length() == length;
	//@ ensures width() == width;
	
	public Rectangle (int length, int width){
		assert length > 0;
		assert width > 0;
		this.length = length;
		this.width = width;
		assert length() == length;
		assert width() == width;
	}
	
	//@ ensures \result > 0;
	/*@ pure */ public int length(){
		return length;
	}
	
	//@ ensures \result >= 0;
	/*@ pure */ public int width(){
		return width;
		}
	
	//@ ensures \result  == length() * width();
	public int area(){
		return length() * width();
	}
	
	//@ ensures \result == length() * width();
	public int perimeter(){
		return 2 * length() + 2 * width();
	}
}
