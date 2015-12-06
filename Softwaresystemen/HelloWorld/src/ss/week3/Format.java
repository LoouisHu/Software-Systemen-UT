package ss.week3;

public class Format {
	
	public static void printLine(String text, double amount) {
		System.out.printf("%-3.30s  %-3.30s%n", text, amount);
	}
	
	public static void main(String[] args) {
		Format.printLine("Test", 10.00);
		Format.printLine("Testtttttttttttttttttt", 150.00);
	}
	
}