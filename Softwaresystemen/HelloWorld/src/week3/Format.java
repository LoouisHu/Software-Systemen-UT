package week3;

public class Format {

	public static void printLine(String text, double amount) { 
		System.out.printf("%-30.30s  %-30.30s%n", text, amount); 
	} 
	 
	public static void main(String[] args) { 
		Format.printLine("Test", 10.00); 
		Format.printLine("Testje", 150.00); 
		} 

}
