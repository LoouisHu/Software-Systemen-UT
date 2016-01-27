package controller;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Observable;
import java.util.Scanner;

import model.*;
import player.*;
import view.*;

public class Client extends Thread {

	// @ private invariant sock != null;
	// @ private invariant in != null;
	// @ private invariant out != null;
	// @ private invariant game != null;
	private Socket sock;
	private BufferedReader in;
	private BufferedWriter out;
	private ClientGame game;
	private List<String> buffer;

	private boolean running;
	
	/**
	 * Creates a new Client that tries to connect to a remote host.
	 * @param host Hostname of the server
	 * @param port Port of the server
	 */
	//@ requires game != null && host != null;
	//@ requires port > 0 && port < 25566;
	public Client(ClientGame game, InetAddress host, int port) {
		this.game = game;
		try {
			sock = new Socket(host, port);
			in = new BufferedReader(new InputStreamReader(sock.getOutputStream()));
			out = new BufferedWriter(new OutputStreamWriter(sock.getInputStream()));
		} catch (IOException e) {
			System.out.println("> ERROR: Could not connect to a server on " + host " with port " + port);
			
		}
		buffer = Collections.synchronizedList(new ArrayList<String>());
	}
	/**
	 * Returns whether the client is connected and running.
	 */
	/* pure */
	public boolean isRunning() {
		return running;
	}
	/**
	 * Sends a message to the connected server.
	 * @param message The message to send, should follow the protocol
	 */
	//@ requires message != null;
	public void sendMessage(String msg) {
		try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			System.out.println("> Connection has been lost. Shutting down..");
			shutdown();
		}
	}
	
	/**
	 * Closes the connection with the server.
	 */
	public void shutdown() {
		try {
			sock.close();
			in.close();
			out.close();
		} catch (IOException e) {
			System.out.println("> Could not shutdown. Please see the manual for more information.\n"
					+ "Nevermind, there is no manual.");
		}
		running = false;
	}
	
	/**
	 * Starts polling for messages from the server.
	 */
	@Override
	public void run(){
		running = in != null;
		while(running) {
			try {
				while (in.ready()) {
					String input = in.readLine();
					System.out.println("[INPUT] " + input);
					buffer.add(input);
				}
			} catch (IOException e){
				System.out.println("> Connection is lost.");
				shutdown();
				
			}
		}
	}
	
	/**
	 * Handles all in coming messages from the server and redirects them too appropriate methods.
	 * @param message
	 */
	/*@ requires message == "WELCOME" 	|| 
 				 message ==	"NAMES"		||
 				 message ==	"NEW"		||
 				 message ==	"TURN" 		||
 				 message ==	"WINNER"	||
 				 message ==	"KICK";*/
	public void handleMessage(String message) {
		Scanner reader = new Scanner(message);
		String command = reader.next();
		String arguments = reader.nextLine();
		if (command.equals("WELCOME")) {
			sendWelcome(arguments);
		} else if (command.equals("NAMES")) {
			sendNames(arguments);
		} else if (command.equals("NEXT")) {
			sendNext(arguments);
		} else if (command.equals("NEW")) {
			sendNew(arguments);
		} else if (command.equals("TURN")) {
			sendTurn(arguments);
		} else if (command.equals("WINNER")) {
			sendWinner(arguments);
		} else if (command.equals("KICK")) {
			sendKick(arguments);
		}
		reader.close();
	}
	
	public void sendWelcome
}
