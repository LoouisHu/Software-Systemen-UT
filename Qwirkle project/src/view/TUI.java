package view;

import java.util.Scanner;

import controller.Client;
import controller.Server;
import controller.ServerController;
import model.Board;
import model.Card;
import model.Player;
import model.Tile;

import java.util.Observable;
import java.util.Observer;
public class TUIView  implements Observer, UI {
	
	private Server server;
	private Client client;
	private ServerController controller;
	Scanner in = new Scanner(System.in);
	
	
	public TUIView(Client client) {
		this.client = client;
	}
	
	public TUIView(ServerController controller) {
		this.controller = controller;
	}
	


	public String waitForMove() {
		System.out.println(client.getBoard().toString());
		displayHand(client);
		String result = null;
		boolean doorgaan = true;
		
		System.out.println("What would you like to do? (MOVE [Tile row column]/ Swap[Tile])");
		while (doorgaan) {
			if (in.hasNextLine()) {
				String message = in.nextLine();
	 			Scanner reader = new Scanner(message);
	 			String command = reader.next();
	 			if (command.equals("MOVE") || 
	 					  command.equals("SWAP") || command.equals("START")) {
	 				result = message;
	 				doorgaan = false;
	 			} else {
	 				result = waitForMove();
	 			}
	 			reader.close();
			}
		}
		return result;
	}			
	
	public void displayHand(Client clientArg) {
		String handString = "Your hand is:";
		for (Tile t : clientArg) {
			handString = handString.concat(" " + t.toString());
		}
		System.out.println(handString);
	}

	public void showMessage(String message) {
		System.out.println(message);
	}
	
	public void showKick(Player p, String reason) {
		System.out.println(p.getName() + "has been kicked, reason: " + reason);
	}

	@Override
	public void showScore(Player p) {
		System.out.println(p.getName() + ": " + p.getScore());
	}

	@Override
	public void showBoard(Board board) {
		System.out.println(board.toString());
		
	}
	
	/*@pure*/public String getCommand() {
		return in.nextLine();
	}
	
	/*@pure*/public Server getServer() {
		return server;
	}
	
	/*@pure*/public ServerController getController() {
		return controller;
	}

	@Override
	public void update(Observable o, Object arg) {
		showBoard(client.getBoard());
	}

}
