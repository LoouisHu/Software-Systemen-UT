package controller;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

import model.Coord;
import model.Move;
import model.Tile;
import model.Tile.Color;
import player.SocketPlayer;

/**
 * Klasse ClientHandler is de communicatie tussen Client en Server. Ook verwerkt
 * het de berichten van Client volgens het Protocol.
 */
public class ClientHandler extends Thread {

	private Server server;
	private Socket socket;
	private BufferedReader in;
	private BufferedWriter out;
	private SocketPlayer socketplayer;
	private Client client;
	private Socket sock;

	/**
	 * Construeert een ClientHandler object. Initialiseert de beide Data
	 * streams.
	 * 
	 */
	public ClientHandler(Server server, Socket socket, SocketPlayer player) {
		this.server = server;
		this.socket = socket;
		this.socketplayer = player;
		try {
			in = new BufferedReader(new InputStreamReader(this.socket.getInputStream()));
			out = new BufferedWriter(new OutputStreamWriter(this.socket.getOutputStream()));
		} catch (IOException e) {
			System.out.println("Fout bij aanmaken van BufferedReader en BufferedWriter in ClientHandler");
		}
	}
	
	public ClientHandler(Client client, Socket socket) {
		this.client = client;
		this.sock = socket;
	}

	/**
	 * Deze methode leest elke regel dat Client stuurt en vervolgens meteen
	 * doorgeeft aan verwerk(message) als de regel niet null is. Als er een
	 * IOException optreedt dan wordt er geconcludeerd dat de Client niet meer
	 * is verbonden en zal de methode remove() van Server worden aangeroepen om
	 * de Client te verwijderen uit de lijst. Vervolgens wordt er shutdown()
	 * aangeroepen.
	 */
	public void run() {
		try {
			while (true) {
				String message = in.readLine();
				if (message != null) {
					sendToServer(message);
				} else {
					throw new IOException();
				}
			}
		} catch (IOException e) {
			shutdown();
		}
	}

	private void sendToServer(String message) {
		server.processMessage(message, this);
	}

	/**
	 * Deze methode kan gebruikt worden om een bericht over de socketverbinding
	 * naar de Client te sturen. Daarna wordt de message doorgegeven aan de
	 * Server die het moet laten zien op de JTextArea van de ServerGUI. Als het
	 * schrijven van het bericht mis gaat, dan concludeert de methode dat de
	 * socketverbinding verbroken is en roept shutdown() aan.
	 * 
	 * @param message
	 */
	public void sendMessage(String message) {
		try {
			out.write(message);
			out.newLine();
			out.flush();
			// server.addMessage(message);
		} catch (IOException e) {
			shutdown();
		}
	}

	/**
	 * Het eerste woord wordt opgeslagen als String 'commando' en wordt
	 * vergeleken of het van de vorm is zoals in het Protocol is afgesproken.
	 * 
	 * Als het commando Protocol.HELLO is, dan wordt het eerste woord na de
	 * commando doorgegeven aan de server bij aanmelding. Dit wordt de player's
	 * naam. De naam mag alleen het alfabet gebruiken met hoofdletters en kleine
	 * letters, mag maar een lengte van 16 bevatten en er mogen geen duplicaten
	 * namen komen.
	 * 
	 * Als het commando Protocol.SWAP is, dan wordt er ижижn of meerdere Tiles
	 * omgewisseld met de pot van de server.
	 * 
	 * Als het commando Protocol.MOVE is, dan wordt er eerst gecheckt of
	 * deze Client aan de beurt is en of er een TURN_BLOCK wordt verwacht en
	 * niet een SET_TILE. Daarna worden de volgende twee woorden bekeken. Deze
	 * twee woorden stellen het blok en de draairichting voor. Eerst wordt er
	 * gecheckt of ze wel in het goede formaat gestuurd zijn en dan wordt het
	 * verandert naar de formaat die bij ons Bord en wordt de draai gedaan en
	 * gebroadcast naar alle spelers in hetzelfde spel. Vervolgens wordt er
	 * gecheckt of het spel is afgelopen. Als dat niet zo is, dan is de volgende
	 * speler aan de beurt.
	 * 
	 * Als het commando Protocol.QUIT is, dan wordt disconnected() aangeroepen
	 * die het verder afhandelt.
	 * 
	 * Als het commando Protocol.CHAT is, dan wordt er gecontroleerd of deze
	 * Client zich in de lobby bevind of in een gestarte spel en wordt het
	 * bericht op de goede plek gebroadcast.
	 * 
	 * @require message != null
	 */
	
	/**
	 * Stuurt de Client van deze ClientHandler een Protocol.KICK.
	 */
	public void kick(String reason) {
		server.getTileBag().returnTiles(socketplayer.getHand());
		sendMessage(Protocol.KICK + socketplayer.getHand().size() + reason);
		// TODO Protocol.TURN Protocol.NEW Protocol.NEXT en mogelijk nog iets in
		// server aanpassen door gekickte speler
		server.getThreads().remove(this);
		shutdown();
	}

	/**
	 * Sluit de socket.
	 */
	public void shutdown() {
		try {
			in.close();
			out.close();
			socket.close();
		} catch (IOException e) {
			System.out.println("Er is iets mis met de socket");
		}
	}

	public SocketPlayer getPlayer() {
		return socketplayer;
	}
	
	public void setPlayerName(String name) {
		getPlayer().setName(name);
	}

	public static Tile convertTextToTile(String s) {
		Tile t;
		char color = s.charAt(0);
		char shape = s.charAt(1);
		t = new Tile(color, shape);
		return t;
	}

}