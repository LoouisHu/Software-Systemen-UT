package controller;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.ConcurrentModificationException;

import model.Board;
import player.HumanPlayer;
import player.Player;

public class Server extends Thread {


	/*
	 * @invariant 0 <= playerNumber < MAXPLAYERS
	 */
	private int playerNumber;
	public static final int MAXPLAYERS = 4;

	/*
	 * @invariant port > 0 && port < 65536
	 */
	private int port;
	private ServerSocket ss;

	/*
	 * @invariant games != null
	 */
	private ArrayList<Game> games;

	/*
	 * @invariant kamers != null
	 */
	private ArrayList<ClientHandler[]> rooms;

	/*
	 * @invariant lobby != null
	 */
	private ArrayList<ClientHandler> lobby;

	/**
	 * Construeert een Server-object en slaat de twee parameters op als
	 * instantievariabele. Verder maakt het de lobbylijst, kamerlijst en
	 * spellijst aan.
	 */
	public Server(int port) {
		this.port = port;
		rooms = new ArrayList<ClientHandler[]>();
		lobby = new ArrayList<ClientHandler>();
		games = new ArrayList<Game>();
	}

	/**
	 * Deze methode blijft nieuwe connecties accepteren en maakt daarmee nieuwe
	 * ClientHandlers aan die vervolgens in de lobbylijst worden gestopt.
	 */
	public void run() {
		try {
			ss = new ServerSocket(port);
			while (true) {
				Socket s = ss.accept();
				ClientHandler ch = new ClientHandler(this, s);
				lobby.add(ch);
				ch.start();
			}
		} catch (IOException e) {
			shutdown();
		}
	}

	/**
	 * Deze methode controleert of de naam die wordt meegegeven al wordt
	 * gebruikt door een andere speler op deze Server.
	 * 
	 */

	/* @requires naam != null && ch != null; */
	public boolean contains(String naam, ClientHandler ch) {
		boolean contains = false;
		for (ClientHandler ch1 : lobby) {
			if (ch1 != ch && !contains) {
				contains = ch1.getNaam().equals(naam);
			}
		}
		if (!contains) {
			for (ClientHandler[] kamer : rooms) {
				for (ClientHandler speler : kamer) {
					if (speler != ch && !contains) {
						contains = speler.getNaam().equals(naam);
					}
				}
			}
		}
		return contains;
	}

	/**
	 * Controleert of de meegegeven ClientHandler zich in de lobby bevindt.
	 * 
	 */
	/* @requires ch!=null */
	public boolean containsCH(ClientHandler ch) {
		return lobby.contains(ch);
	}

	/**
	 * Broadcast de message naar alle ClientHandlers in de lobby.
	 * 
	 * @require message != null
	 */
	public void broadcast(String message) {
		for (ClientHandler ch : lobby) {
			ch.sendMessage(message);
		}
	}

	/**
	 * Geeft de message door aan de methode in ServerGUIListener die het op de
	 * JTextArea gaat zetten.
	 * 
	 * @require message != null;
	 */
	public void addMessage(String message) {
		System.out.println(message);
	}

	/**
	 * Checkt de lobby of er genoeg spelers zijn met dezelfde aantalSpelers om
	 * een spel te starten. Als dat het geval is wordt er een nieuw spel
	 * gestart.
	 * 
	 * @require aantalSpelers >= 2 && aantalSpelers <= 4
	 */
	public boolean check(int aantalSpelers) {
		boolean check = false;
		int aantal = 0;
		ClientHandler[] spelers = new ClientHandler[aantalSpelers];
		for (ClientHandler ch : lobby) {
			if (ch.getAantalSpelers() == aantalSpelers) {
				spelers[aantal] = ch;
				aantal++;
			}
		}
		if (aantal == aantalSpelers) {
			check = true;
			startNewGame(spelers);
		}
		return check;
	}

	/**
	 * Levert alle namen op van de ClientHandlers in de lobby in een String
	 * onderscheiden door een spatie op ClientHandler ch na die is meegegeven.
	 * 
	 * @require ch != null
	 */
	public String getLobby(ClientHandler ch) {
		String players = "";
		for (ClientHandler lobbygast : lobby) {
			if (lobbygast.getNaam() != ch.getNaam()) {
				players += " " + lobbygast.getNaam();
			}
		}
		return players;
	}

	/**
	 * Maakt een nieuwe spel aan met de meegegeven spelers. Vervolgens wordt het
	 * spel in de spellijst gezet en de spelers van dat spel in de kamerlijst.
	 * Ook worden ze verwijderd uit de lobby. De spelers krijgen allemaal een
	 * Protocol.WELCOME met alle spelernamen. De eerste speler krijgt daarna nog
	 * een Protocol.TURN toegestuurd.
	 * 
	 * @require spelers.length >= 2 && spelers.length <= 4
	 * @ensure games.contains(spel) == true
	 */
	public void startNewGame(ClientHandler[] players) {
		Game game;

		if (players.length > 1 && players.length <= MAXPLAYERS) {
			game = new Game(players.length);
			games.add(game);
			rooms.add(players);
			for (ClientHandler ch : players) {
				lobby.remove(ch);
				ch.sendMessage(Protocol.WELCOME);
			}
			players[0].sendMessage(Protocol.TURN);
		}
	}

	/**
	 * Checkt of ClientHandler ch aan de beurt is.
	 * 
	 * @require ch != null
	 */
	public boolean checkBeurt(ClientHandler ch) {
		return games.get(zoekCH(ch)).getBeurt().equals(ch.getNaam());
	}

	/**
	 * Checkt of er een zet moet worden gedaan of een blok moet worden gedraaid.
	 * 
	 * @require ch != null
	 */
	public boolean checkTile(ClientHandler ch) {
		return games.get(zoekCH(ch)).tile();
	}

	/**
	 * Geeft de zet door aan Spel.
	 * 
	 * @require kamer >= 0 && kamer < games.size() && x >= 0 && x <= 8 && y >= 0
	 *          && y <= 8
	 */
	public void doeZet(int kamer, int x, int y) {
		games.get(kamer).doeZet(x, y);
	}

	/**
	 * Checkt op het Bord of het wel een geldige zet is.
	 * 
	 * @require kamer >= 0 && kamer < games.size() && x >= 0 && x <= 8 && y >= 0
	 *          && y <= 8
	 */
	public boolean geldigeZet(int kamer, int x, int y) {
		return games.get(kamer).getBord().geldigVakje(x, y);
	}

	/**
	 * Checkt of het Spel is afgelopen.
	 * 
	 * @require ch != null
	 */
	public boolean checkAfgelopen(ClientHandler ch) {
		boolean afgelopen = false;
		int zoek = zoekCH(ch);
		if (zoek >= 0) {
			afgelopen = games.get(zoek).getBord().isAfgelopen();
		}
		return afgelopen;
	}

	/**
	 * Geeft de beurt aan de volgende speler.
	 * 
	 * @require ch != null
	 */
	public void nextPlayer(ClientHandler ch) {
		int zoek = zoekCH(ch);
		if (zoek >= 0) {
			for (ClientHandler ch1 : rooms.get(zoek)) {
				if (games.get(zoek).getBeurt().equals(ch1.getNaam())) {
					ch1.sendMessage(Protocol.YOUR_TURN);
				}
			}
		}
	}

	/**
	 * Geeft het resultaat van het afgelopen Spel in een String.
	 * 
	 * @require ch != null
	 */
	public String result(ClientHandler ch) {
		return games.get(zoekCH(ch)).getWinnaar();
	}

	/**
	 * Zoekt de kamernummer van ClientHandler ch op.
	 * 
	 * @require ch != null
	 */
	public int zoekCH(ClientHandler ch) {
		int kamer = -1;
		boolean found = false;
		/*
		 * @invariant (\forall int i > 0: !kamers.get(i-1).contains(ch))
		 */
		for (int i = 0; i < rooms.size() && !found; i++) {
			for (ClientHandler ch1 : rooms.get(i)) {
				if (ch == ch1) {
					kamer = i;
					found = true;
				}
			}
		}
		return kamer;
	}

	/**
	 * Stuurt elke speler in de kamer van ClientHandler ch een
	 * Protocol.QUIT_SERVER gevolgd door een aanroep van shutdown in de
	 * ClientHandler van elke speler.
	 * 
	 * @require ch != null
	 */
	public void endGame(ClientHandler ch) {
		int kamernummer = zoekCH(ch);
		for (ClientHandler c : rooms.get(kamernummer)) {
			c.shutdown();
		}
		remove(ch);
	}

	/**
	 * Verwijdert de ClientHandler ch uit de lobby als deze zich in de lobby
	 * bevindt. Anders zit ch in een kamer en wordt de kamer met het
	 * bijbehorende Spel verwijdert uit de kamerlijst en spellijst.
	 * 
	 * @require ch != null
	 */
	public void remove(ClientHandler ch) {
		if (containsCH(ch)) {
			lobby.remove(ch);
		} else {
			int kamernummer = zoekCH(ch);
			if (kamernummer >= 0 && kamernummer < games.size()) {
				synchronized (games) {
					games.remove(kamernummer);
					rooms.remove(kamernummer);
				}
			}
		}
	}

	/**
	 * Roept de shutdown() van elke geconnecte ClientHandler aan en sluit
	 * vervolgens de ServerSocket.
	 */
	public void shutdown() {
		try {
			for (ClientHandler lobbygast : lobby) {
				lobbygast.sendMessage(Protocol.KICK + " Server shutdown");
				lobbygast.shutdown();
			}
		} catch (ConcurrentModificationException c) {
			shutdown();
		}
		try {
			for (ClientHandler[] kamer : rooms) {
				for (ClientHandler speler : kamer) {
					speler.sendMessage(Protocol.KICK + " Server shutdown");
					speler.shutdown();
				}
			}
		} catch (ConcurrentModificationException c) {
			shutdown();
		}
		try {
			if (ss != null) {
				ss.close();
			} else {
				System.out.println("Port is al in gebruik.");
			}
		} catch (IOException e) {
			System.out.println("Er is iets mis met ServerSocket");
		}
	}

	public int getNumber() {
		int result = this.playerNumber;
		this.playerNumber++;
		if (this.playerNumber > MAXPLAYERS - 1) {
			playerNumber = playerNumber % (MAXPLAYERS - 1);
		}
		return result;
	}

	public Game getGame(ClientHandler ch) {
		return games.get(zoekCH(ch));
	}

}
