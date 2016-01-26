package week6;
import java.util.Scanner;

public class HelloWorld {

	private static Scanner in;

	public HelloWorld() {
		// TODO Auto-generated constructor stub
	}

	public static void main(String[] args) {
		boolean doorgaan = true;
		while (doorgaan){	
		in = new Scanner(System.in);
		System.out.println("Enter the name Louis:");
		String name = in.nextLine();
		
		if (name.equals("")){
			doorgaan = false;
		} else { 
			System.out.println(name + ": Hello!");
		}
		}
	}

}
