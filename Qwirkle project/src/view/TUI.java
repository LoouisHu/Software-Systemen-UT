package view;

import java.util.Scanner;

import controller.Client;
import controller.Protocol;
import controller.Server;
import controller.ServerController;
import player.RealPlayer;
import model.Board;
import model.Tile;
import java.util.Observable;
import java.util.Observer;

public class TUI implements Observer {
	
	private Server server;
	private Client client;
	private ServerController controller;
	Scanner in = new Scanner(System.in);
	
	
	public TUI(Client client) {
		this.client = client;
	}
	
	public TUI(ServerController controller) {
		this.controller = controller;
	}
	

	/**
	 * Deze methode wacht op de input MOVE of SWAP. Anders herhaalt hij
	 * zichzelf en opent weer een scanner.
	 * @return
	 */
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
	 			if (command.equals(Protocol.MOVE) || command.equals(Protocol.SWAP)) {
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
	
	/**
	 * Laat de kaarten zien van je hand in de client die het opvraagt.
	 * @param client
	 */
	public void displayHand(Client client) {
		String handString = "Your hand is:  ";
		for (Tile t : client.getThisPlayer().getHand()) {
			handString = handString.concat(" " + t.toString());
		}
		System.out.println(handString);
	}

	public void displayMessage(String message) {
		System.out.println(message);
	}
	
	public void displayKick(RealPlayer p, String reason) {
		System.out.println(p.getName() + "has been kicked, reason: " + reason);
	}

	/**
	 * Showt je huidige score.
	 * @param p
	 */
	public void displayScore(RealPlayer p) {
		System.out.println(p.getName() + ": " + p.getScore());
	}

	/**
	 * Keert de huidige toestand van het board.
	 * @param board
	 */
	public void displayBoard(Board board) {
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
		displayBoard(client.getBoard());
	}

}
