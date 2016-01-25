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


public class TUI extends Observable implements Runnable {
	private int playerNumber;
	private Socket sock;
	private BufferedReader in;
	private BufferedWriter out;
	private Scanner scan;
	
	public TUI() {
		String ip = "";
		String port = "";
		String name = "";
		InetAddress inet = null;
		int portnr = 0;
		
		scan = new Scanner(System.in);
		if(scan.hasNext()) {
			ip = getIP();
		}
		System.out.println(ip);
		if(scan.hasNext()) {
			port = getPort();
		}
		System.out.println(port);
		if(scan.hasNext()) {
			name = getUsername();
		}
		System.out.println(name);
		
		try {
			inet = InetAddress.getByName(ip);
		} catch(UnknownHostException u) {
			System.out.println("Ip-adres fout. Voer een juist ip-adres in.");
		}
		
		try {
			portnr = Integer.parseInt(port);
		} catch(NumberFormatException n) {
			System.out.println("Port nummer fout.");
		}
		
		try {
			if(inet != null && inet != null) {
				sock = new Socket(inet, portnr);
			}
		} catch (IOException e) {
			System.out.println("Socketfout. Voer het juiste ip-adres en de juiste port nummer in.");
		}
		
		if(sock != null) {
			try {
				in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
				out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
			} catch (IOException e) {
				System.out.println("Socketfout. Voer het juiste ip-adres en de juiste port nummer in.");
			}
		
			sendHello(name);
			
			new Thread(this).start();
		}
	}
	
	/**
	 * Stuurt een Protocol.JOIN met een bericht.
	 * @require message != null
	 */
	public void sendHello(String name) {
		sendMessage(Protocol.HELLO + " " + name);
	}
	
	/**
	 * Hiermee kan de Client-kant een bericht sturen naar de server.
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
	 * Ontvangt berichten van de server en stuurt ze door naar verwerk(message) om de berichten te verwerken. Leest per regel.
	 * @require in != null
	 */
	public void run() {
		try {
			while(true) {
				String message = in.readLine();
				if(message != null) {
					verwerk(message);
				}
			}
		} catch (IOException e) {
			shutdown();
		}
	}
	
	public void verwerk(String message) {
		Scanner sc = new Scanner(message);
		String commando = null;
		if(sc.hasNext()) {
			commando = sc.next();
		}
		switch(commando) {
		case Protocol.WELCOME:
			
		}
	}
	
	/**
	 * De socket wordt afgesloten.
	 */
	public void shutdown() {
		try {
			if(sock != null) {
				sock.close();
			}
		} catch (IOException e) {
			System.out.println("Fout bij socket sluiten.");
		}
	}
	
	public String getIP(){
		System.out.print("IP: ");
		return scan.nextLine();
	}
	
	public String getPort(){
		System.out.print("Port: ");
		return scan.nextLine();
	}
	
	public String getUsername(){
		System.out.print("What's your name?: ");
		return scan.nextLine();
	}
	
	public void displayHand(Tile[] hand){
		String handString = "Your hand is:";
		for (Tile t : hand){
			handString = handString.concat(" " + t.toString());
		}
		System.out.println(handString);
	}
	public String displayBoard(String board){
		board = board.toString();
		return board;
	}
	
	
	public static void main(String[] args) {
		new TUI();
	}
	
	
}
