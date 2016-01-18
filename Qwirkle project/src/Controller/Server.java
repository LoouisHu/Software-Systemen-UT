package Controller;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;

import Qwirkle.Board;

public class Server {
	
	private Board board;
	private boolean running;
	private static int portNumber = 666;
	
	public void Server(){
		running = true;
		board = new Board();
		
	}
	
	public void run() {
		ServerSocket serverSocket = null;
		try {
			serverSocket = new ServerSocket(portNumber);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		while(running) {
			try {
				Socket clientSoc;
				clientSoc = serverSocket.accept();
				new Thread(new PlayerHandler(clientSoc, board)).start();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}
}
