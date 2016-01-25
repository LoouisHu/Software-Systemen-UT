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

import Qwirkle.Tile;
import Qwirkle.Tile.Color;

/**
 * Klasse ClientHandler is de communicatie tussen Client en Server. 
 * Ook verwerkt het de berichten van Client volgens het Protocol.
 */
public class ClientHandler extends Thread{
	
	/**
	 * @invariant server != null
	 */
	private Server server;
	
	/**
	 * @invariant socket != null
	 */
	private Socket socket;
	
	/**
	 * @invariant in != null
	 */
	private BufferedReader in;
	
	/**
	 * @invariant out != null
	 */
	private BufferedWriter out;
	
	/**
	 * @invariant naam != null
	 */
	private String naam;
	
	/**
     * Construeert een ClientHandler object.
     * Initialiseert de beide Data streams.
     * @require server != null && socket != null
     */
	public ClientHandler(Server server, Socket socket){
		this.server = server;
		this.socket = socket;
        try {
			in = new BufferedReader(new InputStreamReader(this.socket.getInputStream()));
	        out = new BufferedWriter(new OutputStreamWriter(this.socket.getOutputStream()));
		} catch (IOException e) {
			System.out.println("Fout bij aanmaken van BufferedReader en BufferedWriter in ClientHandler");
		}
    }
	
	/**
	 * Deze methode leest elke regel dat Client stuurt en vervolgens
	 * meteen doorgeeft aan verwerk(message) als de regel niet null is.
	 * Als er een IOException optreedt dan wordt er geconcludeerd dat
	 * de Client niet meer is verbonden en zal de methode remove() van 
	 * Server worden aangeroepen om de Client te verwijderen uit de
	 * lijst. Vervolgens wordt er shutdown() aangeroepen.
	 */
	public void run(){
		try {
			while (true) {
				String message = in.readLine();
				if (message != null) {
					verwerk(message);
				} else {
					throw new IOException();
				}
			}
		} catch (IOException e) {
			server.remove(this);
			shutdown();
		}
	}
	
	 /**
     * Deze methode kan gebruikt worden om een bericht over de 
     * socketverbinding naar de Client te sturen. Daarna wordt
     * de message doorgegeven aan de Server die het moet laten 
     * zien op de JTextArea van de ServerGUI. Als het schrijven
     * van het bericht mis gaat, dan concludeert de methode dat de
     * socketverbinding verbroken is en roept shutdown() aan.
     * @require message != null
     */
	public void sendMessage(String message){
		try {
			out.write(message);
			out.newLine();
			out.flush();
			server.addMessage(message);
		} catch (IOException e) {
			shutdown();
		}
	}
	
	/**
	 * Deze methode plaatst eerst de message die is binnengekomen
	 * op de JTextArea van de ServerGUI. Daarna wordt het eerste 
	 * woord opgeslagen als String 'commando' en vergeleken of het 
	 * van de vorm is zoals in het Protocol is afgesproken. 
	 * 
	 * Als commando Protocol.JOIN is, dan wordt het tweede woord 
	 * bekeken. Dat woord hoort de naam van de Client te zijn.
	 * Het wordt dan gecontroleerd of de naam al bestaat en anders
	 * krijgt het een oplopend nummer achter de originele naam. 
	 * Vervolgens wordt het derde woord bekeken dat het aantal 
	 * spelers hoort te zijn. Als het tussen 1 en 4 ligt, wordt
	 * er een bericht gestuurd naar de Client dat hij geconnect is
	 * en mogelijk nog een spelerlijst als er niet genoeg mensen
	 * zijn om meteen een spel te starten. Als het aantal spelers 0 
	 * wordt er een Protocol.NO_CHALLENGE verstuurd omdat deze niet
	 * geimplementeerd is.
	 * 
	 * Als commando Protocol.SET_TILE is, dan wordt er eerst 
	 * gecheckt of deze Client aan de beurt is en of er een SET_TILE 
	 * wordt verwacht en niet een TURN_BLOCK. Daarna worden de 
	 * volgende twee woorden bekeken. Deze twee woorden stellen het
	 * blok en het cijfer voor. Eerst wordt er gecheckt of ze wel 
	 * in het goede formaat gestuurd zijn en dan wordt het verandert naar 
	 * de formaat die bij ons Bord en wordt er gecheckt of het een 
	 * geldige zet is. Als dat het geval is, wordt de zet gedaan en
	 * gebroadcast naar alle spelers in hetzelfde spel. Vervolgens
	 * wordt er gecheckt of het spel is afgelopen.
	 * 
	 * Als commando Protocol.TURN_BLOCK is, dan wordt er eerst 
	 * gecheckt of deze Client aan de beurt is en of er een TURN_BLOCK 
	 * wordt verwacht en niet een SET_TILE. Daarna worden de 
	 * volgende twee woorden bekeken. Deze twee woorden stellen het
	 * blok en de draairichting voor. Eerst wordt er gecheckt of ze wel 
	 * in het goede formaat gestuurd zijn en dan wordt het verandert naar 
	 * de formaat die bij ons Bord en wordt de draai gedaan en
	 * gebroadcast naar alle spelers in hetzelfde spel. Vervolgens
	 * wordt er gecheckt of het spel is afgelopen. Als dat niet zo is, 
	 * dan is de volgende speler aan de beurt.
	 * 
	 * Als commando Protocol.QUIT is, dan wordt disconnected() aangeroepen 
	 * die het verder afhandelt.
	 * 
	 * Als commando Protocol.CHAT is, dan wordt er gecontroleerd of deze
	 * Client zich in de lobby bevind of in een gestarte spel en wordt 
	 * het bericht op de goede plek gebroadcast.
	 * 
	 * @require message != null
	 */
	public void verwerk(String message){
		server.addMessage(message);
		Scanner sc = new Scanner(message);
		String commando;
		if(sc.hasNext()){
			commando = sc.next();
			switch(commando) {
				case Protocol.HELLO:
					if(server.containsCH(this)){
						if(sc.hasNext()){
							String tempnaam = sc.next();
							if(server.contains(tempnaam, this) && tempnaam.length() < 1 && tempnaam.length() > 16 && !tempnaam.matches("[a-zA-Z]*")) {
								kick("name already exists or name too long or use only letters");
							} else {
								naam = tempnaam;
								sendMessage(Protocol.WELCOME + " " + naam + " " + server.getNumber());
							}
						}
					}
					break;
				case Protocol.SWAP:
					List<Tile> tiles = new ArrayList<Tile>();
					while(sc.hasNext()) {
						tiles.add(convertTextToTile(sc.next()));
					}
					if(tiles.size() <= server.remainingTiles()) {
						List<Tile> swapped = server.getGame(this).swap(tiles);
						String swapcommand = Protocol.NEW;
						for(Tile t:swapped) {
							swapcommand += " " + t.toString();
						}
						sendMessage(swapcommand);
					} else {
						kick("Swapping tiles amount larger than tiles left in the bag");
					}
					break;
				case Protocol.
			}
		}
		
		
		
	}
	
	/**
	 * Broadcast dat het spel is afgelopen en de winnaars naar
	 * alle spelers van het spel waar deze Client zich in
	 * bevind. Vervolgens krijgt elke zo'n speler ook een 
	 * Protocol.QUIT.
	 */
	public void winnaar(){
		server.broadcastIG(this, Protocol.END_GAME + " " + 1 + " " + server.result(this));
		server.endGame(this);
	}

	/**
	 * Stuurt de Client van deze ClientHandler een Protocol.QUIT
	 */
	public void kick(String reason) {
		sendMessage(Protocol.KICK + " " + reason);
		server.remove(this);
		shutdown();
	}
	
	/**
	 * Sluit de socket
	 */
	public void shutdown() {
		try {
			socket.close();
		} catch (IOException e) {
			System.out.println("Er is iets mis met de socket");
		}
	}
	
	/**
	 * Levert de naam op van de Client van deze ClientHandler
	 */
	public String getNaam(){
		return naam;
	}
	
	public Tile convertTextToTile(String s) {
		Tile t;
		char color = s.charAt(0);
		char shape = s.charAt(1);
		t = new Tile(color, shape);
		return t;
	}
}