package controller;

import model.Board;
import model.Tile;
import model.TileBag;
import model.Move;
import player.SocketPlayer;
import model.Coord;
import player.RealPlayer;

import java.util.*;

import view.TUI;

public class Server extends Thread {
	public static final String USAGE = "usage: " + Server.class.getName() + "<port>" + " <aithinktime>";
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
	private TUI view;
	Connect connect;

	/**
	 * Constructs a new server object with a control object think time and a
	 * View.
	 * 
	 * @param controller
	 * @param thinktime
	 * @param ui
	 */
	public Server(ServerController controller, int thinktime, TUI ui) {
		this.view = ui;
		aithinktime = thinktime;
		this.controller = controller;
	}

	/**
	 * Run methods creates a new game by calling the method creatGame(). After
	 * the game is created the game is started with an equal naming. While the
	 * game should keep going this happens, when it shouldn't be the winner is
	 * determined and the server is shutdown.
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
	 * Returns the number of players.
	 * 
	 * @return int
	 */
	/*
	 * @ ensures \result == getThreads().size(); /*@pure
	 */public int getNoOfPlayers() {
		return threads.size();
	}

	/**
	 * Returns the player.
	 * 
	 * @param playerno
	 *            the number assigned by the server to a player.
	 * @return the players which the number is assigned too.
	 */
	/*
	 * @ requires playerno < 4; ensures \result ==
	 * getThreads().get(playerno).getPlayer();
	 */
	public SocketPlayer getPlayer(int playerno) {
		return threads.get(playerno).getPlayer();
	}

	/**
	 * Adds a client to the list threads. A client has a player. In this way
	 * players are connected to a server.
	 * 
	 * @param c
	 */
	/* @ ensures getThreads().contains(c); */
	public void addClient(ClientHandler c) {
		threads.add(c);
	}

	public int addPlayer() {
		int result = playernumber;
		playernumber = (playernumber + 1) % 4;
		return result;
	}

	/**
	 * Starts the game. announces all the players + no and as a last integer the
	 * aithinktime. Sends a complete hand of six Tiles to all players.
	 * Determines and send the first player to play Tiles, done so by
	 * dertermineFirstTurn().
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
	 * Checks if there is more then one/zero player in the game. Checks if the
	 * hand of the player who just played is empty. If the first check passes
	 * and the hand is not empty the next player is send.
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
		} else if (!noValidMoveAvailable(getClientHandler(getPlayer(playerturn))) && tilebag.getTileBagSize() == 0) {
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
	 * Checks if the game is over, if players is 1, the tilebag and player hand
	 * is 0, or there are no valid moves anymore the game is over.
	 * 
	 * @param ch
	 * @return
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
	 * Sends a message too all the clients.
	 * 
	 * @param msg
	 */
	/*
	 * @ requires msg != null; requires getThreads().size() > 0;
	 */
	public void announce(String msg) {
		System.out.println("[FROM SERVER] : " + msg);
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
	 * Als het commando Protocol.SWAP is, dan wordt er ижижn of meerdere Tiles
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
	 * @author Glorious Louis
	 * @param
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
					if (tempname.length() < 1 || tempname.length() > 16 || !tempname.matches("[a-zA-Z]*")) {
						kick(ch, "Name too long or no use of a-zA-Z.");
					} else {
						ch.getPlayer().setName(tempname);
						ch.getPlayer().setNumber(this.addPlayer());
						ch.sendMessage(Protocol.WELCOME + " " + tempname + " " + ch.getPlayer().getNumber());
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
	 * Maakt een string van de lijst van objecten Tile
	 * 
	 * @param Tilelist
	 * @return
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
	 * Checks if a player has all the Tiles he tries to play.
	 * 
	 * @param ch
	 * @param moves
	 *            List <Move>
	 * @return
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
				if (t.getColor().equals(tilehand.getColor()) && t.getShape().equals(tilehand.getShape())) {
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
	 * Checks if a player has all the Tiles he tries to play.
	 * 
	 * @param ch
	 * @param moves
	 *            List <Move>
	 * @return
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
				if (t.getColor().equals(tilehand.getColor()) && t.getShape().equals(tilehand.getShape())) {
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
	 * Checks if a player has a move left. It goes through all the possibilities
	 * and checks if there is atleast one.
	 * 
	 * @param ch
	 *            ClientHandler
	 * @return
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
	 * Calculates the max score for each player's first turn . returns the
	 * number of the player that had the highest score and goes first
	 * 
	 * @param handlerlist
	 * @return
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
	 * Determines who wins the game by comparing all the scores.
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
	 * Creates a new game environment.
	 */
	public void createGame() {
		board = new Board();
		tilebag = new TileBag();
	}

	/**
	 * Closes all the connections and finally the server.
	 */
	public void shutDown() {
		for (int i = 0; i < threads.size(); i++) {
			threads.get(i).shutdown();
		}
		this.interrupt();
	}

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
