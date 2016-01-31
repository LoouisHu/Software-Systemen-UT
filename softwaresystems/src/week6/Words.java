package week6;

import java.util.Scanner;


public class Words {
	
	private static Scanner input;
	
	public static void main(String[] args) {
		boolean breekmeer = false;
		System.out.println("Line (or \"end\"): ");
		input = new Scanner(System.in);
		Scanner lijntjedoen;
		while ((lijntjedoen = new Scanner(input.nextLine())) != null) {
			String woordjesleren;
			int count = 1;
			while (lijntjedoen.hasNext()) {
				woordjesleren = lijntjedoen.next();
				if (woordjesleren.equals("end") && count == 1) {
					breekmeer = true;
					break;
				}
				System.out.println("Word " + (count++) + ": " + woordjesleren);
			}
			lijntjedoen.close();
			if (breekmeer) break;
			System.out.println("Line (or \"end\"): ");
		}
		input.close();
	}
	
}