package week6.voteMachine;

import java.util.List;
import java.util.Map;
import java.util.Observable;
import java.util.Observer;
import java.util.Scanner;

public class VoteTUIView implements VoteView, Observer {

	private VoteMachine machine;

	public VoteTUIView(VoteMachine machine) {
		this.machine = machine;

	}

	public void start() {
		System.out.println("Welcome to the voting machine.");
		System.out.println("Use the HELP command for a list of commands.");

		try (Scanner scanner = new Scanner(System.in)) {
			boolean continueLoop = true;
			while (continueLoop) {
				System.out.print("Command:");
				continueLoop = scanner.hasNextLine() && processCommand(scanner.nextLine());
			}
		}
	}

	private boolean processCommand(String command) {
		boolean continueLoop = true;
		try (Scanner commandScanner = new Scanner(command)) {
			switch (commandScanner.next()) {
			case "VOTE":
				processVoteCommand(commandScanner);
				break;
			case "ADD":
				processAddCommand(commandScanner);
				break;
			case "PARTIES":
				showVotes(machine.getVotes());
				break;
			case "EXIT":
				continueLoop = false;
				break;
			case "HELP":
				printHelp();
				break;
			default:
				showError("Invalid command.");
				break;
			}
		}
		return continueLoop;
	}

	private void processVoteCommand(Scanner commandScanner) {
		if (!commandScanner.hasNextLine()) {
			showError("Expected party name");
		} else {
			String partyName = commandScanner.nextLine();
			machine.vote(partyName);
		}
	}

	private void processAddCommand(Scanner commandScanner) {
		if (!commandScanner.hasNext() || !commandScanner.next().equals("PARTY")) {
			showError("Expected \"PARTY\" keyword.");
		} else if (!commandScanner.hasNextLine()) {
			showError("Expected party name.");
		} else {
			String partyName = commandScanner.nextLine();
			machine.addParty(partyName);
		}
	}

	private void printHelp() {
		System.out.println("Available commands are:");
		System.out.println("\tVOTE [party]");
		System.out.println("\tADD PARTY [party]");
		System.out.println("\tVOTES");
		System.out.println("\tEXIT");
		System.out.println("\tHELP");
	}

	public void showVotes(Map<String, Integer> votes) {
		for (Map.Entry<String, Integer> entry : votes.entrySet()) {
			System.out.println(entry.getKey() + " has " + entry.getValue() + " votes.");
		}
	}

	public void showParties(List<String> parties) {
		for (int i = 0; i < parties.size(); i++) {
			System.out.println(i + ": " + parties.get(i));
		}
	}

	public void showError(String error) {
		System.out.println("Error: " + error);
	}

	@Override
	public void update(Observable arg0, Object arg1) {
		if (!(arg1 instanceof String)) {
			return;
		}

		String property = (String) arg1;
		switch (property) {
		case "party":
			System.out.println("The parties are updated.");
			break;
		case "vote":
			System.out.println("The votes are updated.");
			break;
		}

	}
}