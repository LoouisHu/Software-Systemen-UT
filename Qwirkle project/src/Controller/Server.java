package Controller;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

import Qwirkle.Board;

public class Server {
	
	private Board board;
	private boolean running;
	private static int portNumber;
	
	public void Server(){
		running = true;
		board = new Board();
		
	}
	
	public void run() {
		ServerSocket serverSocket = null;
		try {
			int p = 0;
			serverSocket = new ServerSocket(portNumber);
			portNumber = serverSocket.getLocalPort();
			System.out.println("A player has connected to port: " + portNumber + ".");
			serverSocket.accept();
			System.out.println("Player " + p + " has connected.");
			//if connection is closed, use serverSocket.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		while(running) {
			try {
				Socket clientSoc;
				clientSoc = serverSocket.accept();
				PlayerHandler playerHandler = new PlayerHandler(clientSoc, board);
				new Thread(playerHandler).start();
//				addHandler(playerHandler);
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}
}
