package view;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Scanner;

import Qwirkle.Board;
import Qwirkle.Tile;


public class TUI {
	

	private Scanner in;
	
	public TUI(String ip, int port){

		this.timer = timer;
		this.gebruikcomputer = gebruikcomputer;
		this.cgui = cgui;
		InetAddress inet = null;
		int portnr = 0;
		
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
		
			sendJoin(naam + " " + aantalspelers);
			
			this.start();
		
	}
	
	public String getUsername(){
		System.out.println("What's your name?");
		return in.nextLine();
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
		TUI tui = new TUI("", 6666);
		
		
	}
	
	
}
