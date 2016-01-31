package controller;

import model.Board;
import model.Tile;
import model.TileBag;
import model.Move;
import player.SocketPlayer;
import model.Coord;
import player.RealPlayer;

import java.util.*;

public class Server extends Thread {
	public static final String USAGE = "usage: " + Server.class.getName() 
						  + "<port>" + " <aithinktime>";
	/*
	 * @ invariant getThreads().size() <= 4; invariant
	 * getTileBag().getTileBagSize() <= 108;
	 */
	private List<ClientHandler> threads = new ArrayList<ClientHandler>();
	private TileBag tilebag;
	private Board board;
	private int aithinktime;
	private int playernumber = 0;
	private int playerturn;
	boolean notover;
	private ServerController controller;
	Connect connect;

	/**
	 * Maakt een nieuw Server object met een controller object, thinktime en
	 * een view.
	 * 
	 * @param controller
	 * @param thinktime
	 * @param ui
	 */
	public Server(ServerController controller, int thinktime) {
		aithinktime = thinktime;
		this.controller = controller;
	}

	/**
	 * De run methode start een game door de createGame() en startGame() op te
	 * roepen. Als de boolean gameOver() op false wordt gezet, wordt het spel
	 * gestopt en determineWinner() bepaalt  wie er gewonnen heeft en daarna
	 * sluit de Server socket.
	 */
	public void run() {
		createGame();
		startGame();
		while (!gameOver()) {
			notover = true;
		}
		determineWinner();
		shutDown();
	}

	/**
	 * Retourneert het aantal spelers aka hun threads.
	 * 
	 * @return int
	 */
	/*
	 * @ ensures \result == getThreads().size(); /*@pure
	 */public int getNoOfPlayers() {
		return threads.size();
	}

	/**
	 * Retourneert het type player
	 * 
	 * @param playerno
	 * @return de speler die het aangegeven nummer vasthoudt.
	 */
	/*
	 * @ requires playerno < 4; ensures \result ==
	 * getThreads().get(playerno).getPlayer();
	 */
	public SocketPlayer getPlayer(int playerno) {
		return threads.get(playerno).getPlayer();
	}

	/**
	 * Maakt een nieuwe client aan met een speler.
	 * 
	 * @param ch is de clienthandler die wordt toegevoegd aan de server.
	 */
	/* @ ensures getThreads().contains(c); */
	public void addClient(ClientHandler ch) {
		threads.add(ch);
	}

	public int addPlayer() {
		int result = playernumber;
		playernumber = (playernumber + 1) % 4;
		return result;
	}

	/**
	 * Deze methode start het spel en stuurt aan alle spelers hun naam en nummer.
	 * Als het een AI is neemt het de aithinktime ook mee.
	 */
	/*
	 * @ ensures (\forall int i; 0 <= i & i < getThreads().size();
	 * getThreads().get(i).getPlayer().getHand().size() == 6);
	 */
	public void startGame() {
		String command = Protocol.NAMES;
		for (ClientHandler ch : threads) {
			command = command + " " + ch.getPlayer().getName() + " " + ch.getPlayer().getNumber();
		}
		command = command + " " + aithinktime;

		announce(command);

		for (ClientHandler ch : threads) {
			List<Tile> newtiles = tilebag.getTiles(6);
			ch.getPlayer().setHand(newtiles);
			ch.sendMessage(giveTilesString(newtiles));
		}

		playerturn = determineFirstTurn(threads);
		announce(Protocol.NEXT + determineFirstTurn(threads));
	}

	/**
	 * Kijkt of er meer dan één of nul spelers zijn in het spel. Kijkt of the hand
	 * van de speler die een zet heeft gedaan leeg is. Als er meer dan één of nul spelers
	 * zijn, en de hand van de speler is niet leeg dan krijgt de volgende speler
	 * de beurt.
	 */
	/*
	 * @ ensures getThreads().size() > 1 ==> getPlayerturn() == (getPlayerturn()
	 * + 1) % getThreads().size();
	 */
	public void nextTurn() {
		System.out.println(board.toString());
		System.out.println("Tilebag size:  " + tilebag.getTileBagSize());
		if (threads.size() == 1) {
			RealPlayer player = threads.get(0).getPlayer();
			announce(Protocol.WINNER + " " + player.getNumber());
		} else if (threads.size() == 0) {
			shutDown();
		} else if (getPlayer(playerturn).getHand().size() == 0 && tilebag.getTileBagSize() == 0) {
			getPlayer(playerturn).updateScore(6);
			gameOver();
		} else if (!noValidMoveAvailable(getClientHandler(getPlayer(playerturn))) &&
				  tilebag.getTileBagSize() == 0) {
			announce(Protocol.NEXT + " " + getPlayer(playerturn).getNumber());
		} else {
			playerturn = (playerturn + 1) % threads.size();
			if (getPlayer(playerturn) == null) {
				nextTurn();
			}
		}
		announce(Protocol.NEXT + " " + getPlayer(playerturn).getNumber());
	}

	/**
	 * Kijkt of het spel klaar is, als players 1 is, de tilebag leeg is and de hand van
	 * player leeg is, of er kunnen geen geldige zetten gemaakt worden is het spel klaar.
	 * @return true als er 1 player is of als de tilebag leeg is en er kunnen geen geldige
	 * zetten geplaats worden false als die voorwaarden niet waar zijn.
	 */
	/*
	 * @ ensures getThreads().size() == 1 ==> \result == true; ensures
	 * this.gettilebag().tilebagAmount() == 0 ==> \result == false;
	 */
	public boolean gameOver() {
		boolean result = false;
		if (threads.size() == 1) {
			result = true;
		} else if (tilebag.getTileBagSize() == 0) {
			for (ClientHandler ch : threads) {
				if (!noValidMoveAvailable(ch)) {
					result = false;
				}
			}
		}
		return result;
	}

	/**
	 * Stuurt  een bericht naar alle clienthandlers.
	 * 
	 * @param msg is de het bericht dat wordt gestuurd.
	 */
	/*
	 * @ requires msg != null; requires getThreads().size() > 0;
	 */
	public void announce(String msg) {
		System.out.println("From Server: " + msg);
		for (ClientHandler ch : threads) {
			ch.sendMessage(msg);
		}
	}
	/**
	 * Het eerste woord wordt opgeslagen als String 'commando' en wordt
	 * vergeleken of het van de vorm is zoals in het Protocol is afgesproken.
	 * 
	 * Als het commando Protocol.HELLO is, dan wordt het eerste woord na de
	 * commando doorgegeven aan de server bij aanmelding. Dit wordt de player's
	 * naam. De naam mag alleen het alfabet gebruiken met hoofdletters en kleine
	 * letters, mag maar een lengte van 16.
	 * 
	 * Als het commando Protocol.SWAP is, dan wordt er ¨¦¨¦n of meerdere Tiles
	 * omgewisseld met de pot van de server.
	 * 
	 * Als het commando Protocol.MOVE is, dan wordt er eerst gecheckt of
	 * deze Client aan de beurt is. Daarna worden de volgende twee woorden bekeken. Deze
	 * twee woorden stellen het blok en de draairichting voor. Eerst wordt er
	 * gecheckt of ze wel in het goede formaat gestuurd zijn en dan wordt het
	 * verandert naar de formaat die bij ons Bord en wordt de draai gedaan en
	 * gebroadcast naar alle spelers in hetzelfde spel. Vervolgens wordt er
	 * gecheckt of het spel is afgelopen. Als dat niet zo is, dan is de volgende
	 * speler aan de beurt.
	 *	
	 * @param message, ch
	 * */
	public void processMessage(String message, ClientHandler ch) {
		Scanner sc = new Scanner(message);
		String commando;
		if (sc.hasNext()) {
			commando = sc.next();
			switch (commando) {
				case Protocol.HELLO:
					if (sc.hasNext()) {
						String tempname = sc.next();
						if (tempname.length() < 1 || tempname.length() > 16 ||
								  !tempname.matches("[a-zA-Z]*")) {
							kick(ch, "Name too long or no use of a-zA-Z.");
						} else {
							ch.getPlayer().setName(tempname);
							ch.getPlayer().setNumber(this.addPlayer());
							ch.sendMessage(Protocol.WELCOME + " " + tempname + " " +
							    ch.getPlayer().getNumber());
						}
					}
					break;
				case Protocol.SWAP:
					if (sc.hasNext()) {
						// TODO check turn
						List<Tile> tiles = new ArrayList<Tile>();
						while (sc.hasNext()) {
							tiles.add(ClientHandler.convertTextToTile(sc.next()));
						}
						if (tilebag.getTileBagSize() - tiles.size() >= 0) {
							List<Tile> swapped = tilebag.getTiles(tiles.size());
							tilebag.returnTiles(tiles);
							String swapcommand = Protocol.NEW;
							for (Tile t : swapped) {
								swapcommand += " " + t.toString();
							}
							ch.sendMessage(swapcommand);
							// TODO Protocol.TURN Protocol.NEW Protocol.NEXT
						} else {
							kick(ch, "Swapping tiles amount larger than tiles left in the bag.");
						}
					} else {
						kick(ch, "Must swap at least 1 tile");
					}
					break;
				case Protocol.MOVE:
				// TODO check turn && check message array length
					if (sc.hasNext() && ch.getPlayer().getNumber() == playerturn) {
						String[] string = message.split(" ");
						Tile t = ClientHandler.convertTextToTile(string[1]);
						try {
							int x = Integer.parseInt(string[2]);
							int y = Integer.parseInt(string[3]);
							Coord c = new Coord(x, y);
							Move m = new Move(t, c);
							if (board.validMove(m)) {
								board.boardAddMove(m);
								// sendMessage();// TODO Protocol.TURN Protocol.NEW
								// Protocol.NEXT
							} else {
								kick(ch, "Not a valid move.");
							}
						} catch (NumberFormatException e) {
							kick(ch, "Onjuiste [TILE ROW COLUMN]");
						}
					}
					break;
			}
		}
	}

	
	
	/**
	 * Maakt een string van de lijst van objecten Tile.
	 * 
	 * @param Tilelist is List die geconverteerd wordt naar String.
	 * @return result is de lijst van Tile objecten in een String.
	 */
	public String giveTilesString(List<Tile> tilelist) {
		String result = Protocol.NEW;
		if (tilebag.getTileBagSize() == 0) {
			result = result + " empty";
		} else {
			for (Tile t : tilelist) {
				result = result + " " + t.toString();
			}
		}
		return result;
	}

	/**
	 * Kijkt of een player alle Tiles heeft die hij in een zet wil doen.
	 * 
	 * @param ch is de player.
	 * @param moves zijn de zetten die gemaakt wordt door de player.
	 * @return true als alle Tiles in de player's hand zijn, false als dat niet zo is.
	 */
	public Boolean hasAllTilesMove(ClientHandler ch, List<Move> moves) {
		boolean result = true;
		List<Tile> playedTiles = new ArrayList<Tile>();
		int i = 0;
		for (Move m : moves) {
			Tile t = m.getTile();
			playedTiles.add(t);
		}

		outer: for (Tile t : playedTiles) {
			for (Tile tilehand : ch.getPlayer().getHand()) {
				if (t.getColor().equals(tilehand.getColor()) &&
						  t.getShape().equals(tilehand.getShape())) {
					i++;
					continue outer;
				}
			}
		}
		if (i != moves.size()) {
			result = false;
		}
		return result;
	}
	
	/**
	 * Hanteert een player kick.
	 * Stuurt een bericht naar alle clients met het aantal Tiles die terug naar de tilebag
	 * vervoerd worden.
	 * @param ch is player die gekickt wordt.
	 * @param reason is de reden waarvoor een player gekickt wordt.
	 */
	public void kick(ClientHandler ch, String reason) {
		List<Tile> hand = ch.getPlayer().getHand();
		if (hand != null) {
			tilebag.returnTiles(hand);
		}
		announce("KICK " + ch.getPlayer().getNumber() + " " + hand.size() + " " + reason);
		if (playerturn == ch.getPlayer().getNumber()) {
			nextTurn();
		}
		threads.remove(ch);
	}

	/**
	 * Kijkt of player alle Tiles heeft die hij probeert te ruilen.
	 * 
	 * @param ch is de player
	 * @param moves is de List die wordt gecheckt.
	 * @return true als de player alle tiles heeft in moves, false als de player die niet heeft.
	 */
	public Boolean hasAllTilesSwap(ClientHandler ch, List<Move> moves) {
		boolean result = true;
		List<Tile> playedTiles = new ArrayList<Tile>();
		int i = 0;
		for (Move s : moves) {
			Tile c = s.getTile();
			playedTiles.add(c);
		}

		outer: for (Tile t : playedTiles) {
			for (Tile tilehand : ch.getPlayer().getHand()) {
				if (t.getColor().equals(tilehand.getColor()) &&
						  t.getShape().equals(tilehand.getShape())) {
					i++;
					continue outer;
				}
			}
		}
		if (i != moves.size()) {
			result = false;
		}
		return result;
	}

	/**
	 * Kijkt of een player nog een geldige zet kan doen, als die wordt gevonden
	 * retourneert de methode true.
	 * 
	 * @param ch is de player
	 * @return true als er een geldige zet is gevonden, false als die er niet is.
	 */
	/*
	 * @ ensures (\forall int i, j, k; 0 <= i & i < 183 & 0 <= k & k <= 183 & 0
	 * <= j & j < ch.getPlayer().getHand().size();
	 * this.getBoard().isValidMove(new Move(ch.getPlayer().getHand().get(i), i,
	 * k)) ==> \result == true);
	 */
	public boolean noValidMoveAvailable(ClientHandler ch) {
		boolean result = true;
		if (ch.getPlayer().getHand().size() == 0) {
			result = true;
		} else {
			for (int i = 0; i < ch.getPlayer().getHand().size(); i++) {
				for (int y = 0; y < 183; y++) {
					for (int x = 0; x < 183; x++) {
						Move move = new Move(ch.getPlayer().getHand().get(i), new Coord(x, y));
						if (board.validMove(move)) {
							result = false;
							break;
						}

					}
				}
			}
		}
		return result;
	}

	/**
	 * Berekent de max score voor elke spelers eerste beurt. Retourneert de playernumber van de
	 * player met de hoogste score die als eerst mag beginnen.
	 * @param handlerlist zijn de players
	 * @return playerNo van de player met de hoogste score.
	 */
	public int determineFirstTurn(List<ClientHandler> handlerlist) {
		Map<Integer, Integer> playerscores = new HashMap<Integer, Integer>();
		int[] score = new int[12];
		int result = 0;
		for (ClientHandler ch : handlerlist) {
			int maxscore = 0;
			for (Tile t : ch.getPlayer().getHand()) {
				switch (t.getColor()) {
					case RED:
						score[0]++;
						break;
					case ORANGE:
						score[1]++;
						break;
					case YELLOW:
						score[2]++;
						break;
					case GREEN:
						score[3]++;
						break;
					case BLUE:
						score[4]++;
						break;
					case PURPLE:
						score[5]++;
						break;
				}
				switch (t.getShape()) {
					case CIRCLE:
						score[6]++;
						break;
					case CROSS:
						score[7]++;
						break;
					case DIAMOND:
						score[8]++;
						break;
					case SQUARE:
						score[9]++;
						break;
					case STAR:
						score[10]++;
						break;
					case CLOVER:
						score[11]++;
						break;
				}
				for (int i = 0; i < 12; i++) {
					if (score[i] > maxscore) {
						maxscore = score[i];
					}
				}
				playerscores.put(ch.getPlayer().getNumber(), maxscore);
			}
			int maxscorevalue = Collections.max(playerscores.values());
			for (Map.Entry<Integer, Integer> entry : playerscores.entrySet()) {
				if (entry.getValue() == maxscorevalue) {
					result = entry.getKey();
					break;
				}
			}
		}
		return result;
	}

	/**
	 * Kijkt wie de winnaar is van het spel door alle scores te vergelijken.
	 */
	public void determineWinner() {
		int highscore = 0;
		int winnernumber = 0;
		for (ClientHandler ch : threads) {
			if (ch.getPlayer().getScore() > highscore) {
				highscore = ch.getPlayer().getScore();
				winnernumber = ch.getPlayer().getNumber();
			}
		}
		announce("WINNER " + winnernumber);
		shutDown();
	}

	/**
	 * Maak een nieuwe Game.
	 */
	public void createGame() {
		board = new Board();
		tilebag = new TileBag();
	}

	/**
	 * Sluit alle connecties met de clients en sluit de server.
	 */
	public void shutDown() {
		for (int i = 0; i < threads.size(); i++) {
			threads.get(i).shutdown();
		}
		this.interrupt();
	}

	/**
	 * Gets de ClientHandler van een player.
	 * @param player is
	 * @return de ClientHandler van een player
	 */
	public ClientHandler getClientHandler(RealPlayer player) {
		ClientHandler found = null;
		for (ClientHandler ch : threads) {
			if (ch.getPlayer() == player) {
				found = ch;
			}
		}
		return found;
	}

	/* @pure */public List<ClientHandler> getThreads() {
		return threads;
	}

	/* @pure */public int getPlayerturn() {
		return playerturn;
	}

	/* @pure */public TileBag getTileBag() {
		return tilebag;
	}

	/* @pure */public Board getBoard() {
		return board;
	}

	/* @pure */public ServerController getController() {
		return controller;
	}

}
