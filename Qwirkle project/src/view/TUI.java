package view;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.Observable;
import java.util.Scanner;

import controller.Protocol;
import model.Board;
import model.Tile;
import player.ComputerPlayer;
import player.HumanPlayer;
import player.Player;

public class TUI extends Observable implements Runnable {
	private int playerNumber;
	private Socket sock;
	private BufferedReader in;
	private BufferedWriter out;
	private Scanner scan;
	private String name;
	private Board board;
	private Player player;

	public TUI() {
		String ip = "";
		String port = "";
		name = "";
		InetAddress inet = null;
		int portnr = 0;
		board = new Board();

		scan = new Scanner(System.in);
		System.out.print("IP: ");
		if (scan.hasNext()) {
			ip = scan.next();
		}
		System.out.print("Port: ");
		if (scan.hasNext()) {
			port = scan.next();
		}
		System.out.print("Name: ");
		if (scan.hasNext()) {
			name = scan.next();
		}

		try {
			inet = InetAddress.getByName(ip);
		} catch (UnknownHostException u) {
			System.out.println("Ip-adres fout. Voer een juist ip-adres in.");
		}

		try {
			portnr = Integer.parseInt(port);
		} catch (NumberFormatException n) {
			System.out.println("Port nummer fout.");
		}

		try {
			if (inet != null) {
				sock = new Socket(inet, portnr);
			}
		} catch (IOException e) {
			System.out.println("Socketfout. Voer het juiste ip-adres en de juiste port nummer in.");
		}

		if (sock != null) {
			try {
				in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
				out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
			} catch (IOException e) {
				System.out.println("Socketfout. Voer het juiste ip-adres en port nummer in.");
			}

			sendHello(name);
			new Thread(this).start();
		}
	}

	/**
	 * Stuurt een Protocol.JOIN met een bericht.
	 * 
	 * @require message != null
	 */
	public void sendHello(String nameArg) {
		sendMessage(Protocol.HELLO + " " + nameArg);
	}

	/**
	 * Hiermee kan de Client-kant een bericht sturen naar de server.
	 * 
	 * @require message != null
	 */
	public void sendMessage(String message) {
		try {
			out.write(message);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			shutdown();
		}
	}

	/**
	 * Ontvangt berichten van de server en stuurt ze door naar verwerk(message)
	 * om de berichten te verwerken. Leest per regel.
	 * 
	 * @require in != null
	 */
	public void run() {
		try {
			while (true) {
				String message = in.readLine();
				if (message != null) {
					process(message);
				}
			}
		} catch (IOException e) {
			shutdown();
		}
	}

	public void process(String message) {
		Scanner sc = new Scanner(message);
		String commando = null;
		if (sc.hasNext()) {
			commando = sc.next();
		}
		switch (commando) {
			case Protocol.WELCOME:
				if (sc.hasNext()) {
					name = sc.next();
					player = new HumanPlayer(name, board);
				}
				if (sc.hasNext()) {
					playerNumber = Integer.parseInt(sc.next());
				}
				break;
			case Protocol.WINNER:
				if (sc.hasNext()) {
					System.out.println("The winner: " + sc.next());
				}
				break;
			case Protocol.NEXT:
				if (sc.hasNext()) {
					String number = sc.next();
					if (playerNumber == Integer.parseInt(number)) {
						System.out.println("Your turn");
						if (player instanceof ComputerPlayer){
							player.makeMove(null, null);
						} else {
							player.makeMove(move);
						}
						
					} else {
						System.out.println("Next player: " + player);
					}
				}
				break;
		}
	}

	/**
	 * De socket wordt afgesloten.
	 */
	public void shutdown() {
		try {
			if (sock != null) {
				sock.close();
			}
		} catch (IOException e) {
			System.out.println("Fout bij socket sluiten.");
		}
	}

	public void displayHand(Tile[] hand) {
		String handString = "Your hand is:";
		for (Tile t : hand) {
			handString = handString.concat(" " + t.toString());
		}
		System.out.println(handString);
	}

	public String displayBoard() {
		return this.board.toString();
	}

	public static void main(String[] args) {
		new TUI();
	}
}
