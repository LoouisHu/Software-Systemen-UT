package controller;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.List;
import java.util.Observable;
import java.util.Scanner;

import view.TUI;
import model.Board;
import model.Coord;
import model.Tile;
import player.HumanPlayer;
import player.SocketPlayer;
import model.Move;
import player.RealPlayer;
import player.RetardedPlayer;

public class Client extends Observable {

	private List<RealPlayer> players;
	private boolean gameend = false;
	private Board board;
	private HumanPlayer thisplayer;
	private TUI view;
	private int tilebag;
	private ClientHandler clienthandler;
	private int aithinktime;
	private boolean completemoveprocessed = false;
	public static final String USAGE = "usage: " + Client.class.getName() + "<port>" + "<Host> " + "<Name>";

	public static void main(String[] args) {
		if (args.length != 4) {
			System.out.println(USAGE);
			System.exit(0);
		}

		InetAddress host = null;
		int port = 0;

		try {
			host = InetAddress.getByName(args[1]);
		} catch (UnknownHostException e) {
			System.out.println("Error host address");
			System.exit(0);
		}

		try {
			port = Integer.parseInt(args[0]);
		} catch (NumberFormatException e) {
			System.out.println("Not a valid port number");
			System.exit(0);
		}

		try {
			Socket sock = new Socket(host, port);
			new Client(sock, args[2], args[3]);
		} catch (IOException e) {
			System.exit(0);
		}
	}

	/**
	 * Creates a new client connecting to the given socket constructing a new
	 * player of type playertype with the name name. The args come from the args
	 * list in the main method.
	 * 
	 * @param sockarg
	 * @param name
	 * @param playertype
	 */
	/*
	 * @ ensures this.getClientHandler().getSocket() == sockarg; ensures
	 * this.getThisPlayer().getName() == name;
	 */
	public Client(Socket sockarg, String name, String playertype) {
		this.board = new Board();
		this.view = new TUI(this);
		this.players = new ArrayList<RealPlayer>();
		switch (playertype) {
		case "HUMAN":
			this.thisplayer = new HumanPlayer(name, this);
			break;
		case "AI":
			this.thisplayer = new RetardedPlayer(name, this, 2000); // de
																	// AIThinkTime
																	// is
																	// gehardcoded,
																	// moet nog
																	// van
																	// server
																	// krijgen.
			break;
		}
		clienthandler = new ClientHandler(this, sockarg);
		this.addObserver(view);
		clienthandler.sendMessage(Protocol.HELLO + " " + getThisPlayer().getName());
	}

	/**
	 * Handles all in coming messages from the server and redirects them too
	 * appropriate methods.
	 * 
	 * @param message
	 */
	/*
	 * @ requires message == "WELCOME" || message == "NAMES" || message == "NEW"
	 * || message == "TURN" || message == "WINNER" || message == "KICK";
	 */
	public void handleMessage(String message) {
		Scanner sc = new Scanner(message);
		String command = null;
		if (sc.hasNext()) {
			command = sc.next();
		}
		switch (command) {
		case Protocol.WELCOME:
			handleWelcome(message);
			break;
		case Protocol.NAMES:
			handleNames(message);
			break;
		case Protocol.NEXT:
			handleNext(message);
			break;
		case Protocol.NEW:
			handleNew(message);
			break;
		case Protocol.TURN:
			handleTurn(message);
			break;
		case Protocol.KICK:
			handleKick(message);
			break;
		case Protocol.WINNER:
			handleWinner(message);
			break;
		}

		sc.close();
	}

	/**
	 * Deze methode wordt opgeroepen als de client een WELCOME terugkrijgt.
	 * Server geeft playername en number terug als alles in orde is.
	 * 
	 * @param args
	 */
	/*
	 * @ ensures this.getThisPlayer().getNumber() == 0 ||
	 * this.getThisPlayer().getNumber() == 1 || this.getThisPlayer().getNumber()
	 * == 2 || this.getThisPlayer().getNumber() == 3;
	 */
	private void handleWelcome(String args) {
		Scanner reader = new Scanner(args);
		reader.next();
		int playernumber = Integer.parseInt(reader.next());
		getThisPlayer().setNumber(playernumber);
		reader.close();
	}

	/**
	 * Deze methode wordt opgeroepen als de server een NAMES terugstuurt naar de
	 * client. Server geeft alle playernames met de AITime terug als het spel
	 * begint.
	 * 
	 * @param args
	 */
	/*
	 * @ ensures this.getAIThinkTime() != \old(this.getAIThinkTime()); ensures
	 * this.getPlayers().size() >= \old(this.getPlayers().size());
	 */
	private void handleNames(String args) {
		Scanner reader = new Scanner(args);
		while (reader.hasNext()) {
			String playername = reader.next();
			if (!reader.hasNext()) {
				aithinktime = Integer.parseInt(playername);
				break;
			}
			int playernumber = Integer.parseInt(reader.next());
			if (playernumber != getThisPlayer().getNumber()) {
				players.add(new SocketPlayer(playername, playernumber));
			}
		}
		view.displayBoard(board);
		tilebag = 108 - (6 * (players.size() + 1));
		reader.close();
	}

	/**
	 * Deze methode wordt opgeroepen als de server een NEXT terugstuurt. Server
	 * geeft aan wie er aan de beurt is.
	 * 
	 * @param args
	 */
	/*
	 * @ ensures this.getThisPlayer().getHand() !=
	 * \old(this.getThisPlayer().getHand());
	 */
	private void handleNext(String args) {
		Scanner reader = new Scanner(args);
		if (getThisPlayer() == getPlayer(Integer.parseInt(reader.next()))) {
			HumanPlayer p = new RetardedPlayer("louis", this);
			String message = "";
			view.displayMessage(p.determineMove(board, this.getThisPlayer().getHand()).);
			message = thisplayer.determineMove(board, thisplayer.getHand());
			view.displayMessage("Tilebag size : " + tilebag);
			Scanner readmessage = new Scanner(message);
			String command = readmessage.next();
			if (readmessage.hasNext() && command.equals(Protocol.MOVE)) {
				List<Move> moves = stringToMoveList(readmessage.nextLine());
				int notvalid = 0;
				for (Move m : moves) {
					if (!board.validMove(m)) {
						notvalid++;
					}
				}
				if (!moves.isEmpty() && hasAllTilesMove(moves) && notvalid == 0) {
					for (Move m : moves) {
						board.boardAddMove(m);
						thisplayer.removeFromHandByMove(m);
					}
					clienthandler.sendMessage(message);
					reader.close();
					readmessage.close();

				} else {
					view.displayMessage("Try again");
					handleNext(command);
				}
			} else if (message.equals(Protocol.SWAP)) {
				List<Move> moves = stringToMoveList(reader.nextLine());
				if (tilebag < moves.size() || !hasAllTilesMove(moves)) {
					view.displayMessage("Try again, stack size: " + tilebag);
					handleNext(message);
				} else {
					for (Move m : moves) {
						thisplayer.removeFromHandByMove(m);
					}
					clienthandler.sendMessage(message);
					reader.close();
				}
			} else {
				handleNext(message);
			}
		}
	}

	/**
	 * Deze methode wordt door de handleMessage() opgeroepen als het protocol
	 * NEW is. De server geeft dan aan wie er aan de beurt is.
	 * 
	 * @param args
	 */
	/*
	 * @ ensures this.getThisPlayer().getHand() !=
	 * \old(this.getThisPlayer().getHand());
	 */
	private void handleNew(String args) {
		Scanner reader = new Scanner(args);
		while (reader.hasNext()) {
			String tilestring = reader.next();
			if (!tilestring.equals("empty")) {
				char[] tilechars = tilestring.toCharArray();
				synchronized (thisplayer) {
					thisplayer.getHand().add(new Tile(tilechars[0], tilechars[1]));
				}
			} else {
				view.displayMessage("No new Tiles available");
			}
		}
		reader.close();
	}

	/**
	 * Deze methode wordt aangeroepen als de message begint met een TURN.
	 *
	 * @param args
	 */
	/*
	 * @ ensures args.length() == 10 ==> this.getBoard() ==
	 * \old(this.getBoard()); ensures args.length() != 10 ==> this.getBoard() !=
	 * \old(this.getBoard());
	 */
	private void handleTurn(String args) {
		Scanner reader = new Scanner(args);
		RealPlayer player = getPlayer(Integer.parseInt(reader.next()));
		String word = reader.next();
		if (word.equals("empty")) {
			view.displayMessage("Tiles have been swapped.");
		} else {
			List<Move> moves = stringToMoveList(word + " " + reader.nextLine());
			if (tilebag > moves.size()) {
				tilebag -= moves.size();
			} else if (tilebag < moves.size()) {
				tilebag = 0;
			}
			player.updateScore(board.decideScore(moves));
			for (Move p : moves) {
				board.boardAddMove(p);
			}

		}
		setChanged();
		notifyObservers();
		view.displayScore(player);
		reader.close();
	}

	/**
	 * De server geeft door dat er iemand gewonnen heeft.
	 * 
	 * @param args
	 */
	/* @ ensures this.getGameEnd() == true; */
	private void handleWinner(String args) {
		Scanner reader = new Scanner(args);
		int winner = Integer.parseInt(reader.next());
		view.displayMessage("Player: " + getPlayer(winner).getName() + " won the game");
		reader.close();
		gameend = true;
		shutDown();
	}

	/**
	 * Get's called by the method handleMessage() if it starts with KICK. This
	 * method get everything sorted out when a player is kicked.
	 * 
	 * @param args
	 */
	/* @ ensures tileBag > \old(stackSize); */
	private void handleKick(String args) {
		Scanner reader = new Scanner(args);
		RealPlayer player = getPlayer(Integer.parseInt(reader.next()));
		int tilesBack = Integer.parseInt(reader.next());
		tilebag += tilesBack;
		String reason = reader.nextLine();
		if (player.equals(thisplayer)) {
			view.displayKick(player, reason);
			view.displayMessage("You have been kicked: " + reason);
			reader.close();
			shutDown();
		}
		reader.close();
	}

	/**
	 * Checks if the players has all Tiles he wants to play.
	 * 
	 * @param moves
	 */
	/*
	 * @ ensures (\forall int i; 0 <= i & i <
	 * this.getThisPlayer().getHand().size(); (\forall int j; 0 <= j & j <
	 * moves.size(); this.getThisPlayer().getHand().get(i).getColor() ==
	 * moves.get(j).getTile().getColor() &&
	 * this.getThisPlayer().getHand().get(i).getShape() ==
	 * moves.get(j).getTile().getShape()) ==> \result == true);
	 */
	public Boolean hasAllTilesMove(List<Move> moves) {
		boolean result = true;
		List<Tile> playedtiles = new ArrayList<Tile>();
		int i = 0;
		for (Move m : moves) {
			Tile t = m.getTile();
			playedtiles.add(t);
		}

		outer: for (Tile t : playedtiles) {
			for (Tile tilehand : thisplayer.getHand()) {
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
	 * This methods converts a string with correctly formatted Move. to a List
	 * <Move> JML is including Spacebar and requires there to not be a space at
	 * the end.
	 * 
	 * @param movestring
	 * @return List<Swtich>
	 */
	/* @ requires (movestring.length() - 6) % 3 == 0; */
	public List<Move> stringToMoveList(String movestring) {
		Scanner sc = new Scanner(movestring);
		List<Move> moves = new ArrayList<Move>();
		while (sc.hasNext()) {
			String Tilestring = sc.next();
			char[] Tilechars = Tilestring.toCharArray();
			if (Tilechars.length != 2) {
				break;
			}
			Tile Tile = new Tile(Tilechars[0], Tilechars[1]);
			moves.add(new Move(Tile));
			// catches an invalid Tile
			if (!sc.hasNext()) {
				break;
			}
		}
		sc.close();
		return moves;
	}

	/**
	 * Returns the player of which the playernumber is given.
	 * 
	 * @param playernumber
	 * @return
	 */
	/* @pure */public RealPlayer getPlayer(int playernumber) {
		RealPlayer result = null;
		if (getThisPlayer().getNumber() == playernumber) {
			result = thisplayer;
		} else {
			for (RealPlayer player : players) {
				if (player.getNumber() == playernumber) {
					result = player;
				}
			}
		}
		return result;
	}

	/* @pure */public List<RealPlayer> getPlayers() {
		return players;
	}

	/* @pure */public HumanPlayer getThisPlayer() {
		return thisplayer;
	}

	/* @pure */public ClientHandler getClientHandler() {
		return clienthandler;
	}

	/* @pure */public int getAIThinkTime() {
		return aithinktime;
	}

	/* @pure */boolean completeMoveProcessed() {
		return completemoveprocessed;
	}

	/* @pure */public int getPlayerNumber() {
		return thisplayer.getNumber();
	}

	/* @pure */public Board getBoard() {
		return this.board;
	}

	/* @pure */public TUI getView() {
		return view;
	}

	/* @pure */public int getTileBag() {
		return tilebag;
	}

	/* @pure */public boolean getGameEnd() {
		return gameend;
	}

	public void shutDown() {
		clienthandler.shutdown();
		System.exit(0);
	}
}