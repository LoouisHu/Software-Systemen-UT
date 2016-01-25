package controller;

import player.Player;

import java.net.*;
import java.io.*;

public class Connection extends Thread {
	private Game game;
	private Client client;
	private Socket sock;
	
	private Player player;
	
	private BufferedReader in;
	private BufferedWriter out;
	
	public Connection(Game server, Socket sock, Player player){
		this.game = server;
		this.sock = sock;
		this.player = player;
	}
	
	public Connection(Client client, Socket sock) {
		this.client = client;
		this.sock = sock;
	}
	
	public void openConnection(){
		try {
			in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
			out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
		} catch (IOException e) {

		}
	}
}
