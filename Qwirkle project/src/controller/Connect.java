package controller;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import player.SocketPlayer;
import view.TUI;

public class Connect extends Thread {
	
	private int port;
	private Server server;
	private TUI view;
	
	public Connect(Server serverArg, int portArg, TUI view) {
		server = serverArg;
		port = portArg;
		this.view = view;
		this.start();
		
	}
	public void run() { 
		ServerSocket serversocket = null;
		boolean acceptingNewClient = true;
		
		try { 
			serversocket = new ServerSocket(port);
			int nr = server.getNoOfPlayers();
			
			while (acceptingNewClient) {
				if (nr == 4) {
					acceptingNewClient = false;
				}	
				Socket clientsocket = serversocket.accept();
				ClientHandler clienthandler = 
						  new ClientHandler(server, clientsocket, new SocketPlayer());
				view.displayMessage("New player connected!");
				server.addClient(clienthandler);
			} 
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			try {
				serversocket.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
}
