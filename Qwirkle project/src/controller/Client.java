package controller;


import view.TUIView;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.*;
import exceptions.*;
import model.Board;
import model.Card;
import model.LocalPlayer;
import model.NetworkPlayer;
import model.Move;
import player.Player;
import player.;
import model.Switch;

import java.io.IOException;

public class Client extends Observable {

	private List<Player> players;
	private boolean gameend = false;
	private Board board;
	private LocalPlayer thisplayer;
	private TUIView view;
	private int stackSize;
	private ClientHandler clienthandler;
	private int aithinktime;
	private boolean completemoveprocessed = false;
	public static final String USAGE =
			  "usage: " + Client.class.getName() + "<port>" + "<Host> "  + "<Name>";
	
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
			System.out.println("ERROR: no valid hostname!");
			System.exit(0);
		}

		try {
			port = Integer.parseInt(args[0]);
		} catch (NumberFormatException e) {
			System.out.println("ERROR: no valid portnummer!");
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
	 * Creates a new client connecting to the given socket constructing a new player of type
	 * playertype with the name name. The arguments come from the arguments list in the main
	 * method.
	 * @param sockarg
	 * @param name
	 * @param playertype
	 */
	/*@ ensures this.getClientHandler().getSocket() == sockarg; 
	 	ensures this.getThisPlayer().getName() == name;*/
	public Client(Socket sockarg, String name, String playertype) {
		this.board = new Board();
		this.view = new TUIView(this);
		this.players = new ArrayList<Player>();
		switch (playertype) {
			case "HUMAN" : this.thisplayer = new LocalPlayer(name, this);
						break;
			case "AI" 	 : this.thisplayer = new StupidAI(name, this, 2000);
						break;
		}
		clienthandler = new ClientHandler(this, sockarg);
		this.addObserver(view);
		clienthandler.sendMessage("HELLO " + getThisPlayer().getName());
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
			handleWelcome(arguments);
		} else if (command.equals("NAMES")) {
			handleNames(arguments);
		} else if (command.equals("NEXT")) {
			handleNext(arguments);
		} else if (command.equals("NEW")) {
			handleNew(arguments);
		} else if (command.equals("TURN")) {
			handleTurn(arguments);
		} else if (command.equals("WINNER")) {
			handleWinner(arguments);
		} else if (command.equals("KICK")) {
			handleKick(arguments);
		}
		reader.close();
	}
	
	/**
	 * Get's called by the method handleMessage() if it starts with HELLO.
	 * Set the given playernumber
	 * @param arguments String to be decoded
	 */
	/*@ ensures this.getThisPlayer().getNumber() == 0 ||
	  			this.getThisPlayer().getNumber() == 1 ||
	  			this.getThisPlayer().getNumber() == 2 ||
	  			this.getThisPlayer().getNumber() == 3;*/
	private void handleWelcome(String arguments) {
		Scanner reader = new Scanner(arguments);
		reader.next();
		int playernumber = Integer.parseInt(reader.next());
		getThisPlayer().setNumber(playernumber);
		reader.close();
	}
	
	/**
	 * Get's called by the method handleMessage() if it starts with NAME.
	 * @param arguments String to be decoded
	 */
	/*@ ensures this.getAIThinkTime() != \old(this.getAIThinkTime());
		ensures this.getPlayers().size() >= \old(this.getPlayers().size()); */
	private void handleNames(String arguments) {
		Scanner reader = new Scanner(arguments);
		while (reader.hasNext()) {
			String playername = reader.next();
			if (!reader.hasNext()) {
				aithinktime = Integer.parseInt(playername);
				break;
			}
			int playernumber = Integer.parseInt(reader.next());
			if (playernumber != getThisPlayer().getNumber()) {
				players.add(new NetworkPlayer(playername, playernumber));
			}
		}
		view.showBoard(board); 
		stackSize = 108 - (6 * (players.size() + 1));
		reader.close();
	}
	
	/**
	 * Get's called by the method handleMessage() if it starts with NEXT.
	 * This method handles the input of the player and in turn sends it to the server.
	 * @param arguments String to be decoded
	 */
	/*@ ensures this.getThisPlayer().getHand() != \old(this.getThisPlayer().getHand());*/
	private void handleNext(String arguments) {
		Scanner reader = new Scanner(arguments);
		//If it the players turn
		if (getThisPlayer() == getPlayer(Integer.parseInt(reader.next()))) {
			String message = "0";
			message = thisplayer.determineMove(board, thisplayer.getHand());
			view.showMessage("Stack size : " + stackSize);
			
			//If there is an actual move put in continue 
			if (!message.equals("0")) {
				Scanner readmessage = new Scanner(message);
				String command = readmessage.next();
				if (readmessage.hasNext()) {
					
					//Handle the move.
					if (command.equals("MOVE")) {
						List<Place> moves = stringToPlaceList(readmessage.nextLine());
						
						//Only if it is not empty
						if (!moves.isEmpty()) {
							try {
								//If it has all cards and the moves are valid
								if (hasAllCardsMove(moves) && board.isValidMoveList(moves)) {
									//Place the, on the board
									for (Place p: moves) {
										board.placeCard(p);
										thisplayer.removePlaceFromHand(p);
									}
									clienthandler.sendMessage(message);
									reader.close();
									readmessage.close();
								} else {
									//If not try again.
									view.showMessage("Try again");
									handleNext(arguments);
								}
							} catch (LoneSpotException | NoEmptySpotException | 
									  NoValidCombinationException
									| LineTooLongException e) {
								view.showMessage(e.getMessage());
								handleNext(arguments);
							}
						} else {
							view.showMessage("Try again");
							handleNext(arguments);
						}
					} else if (command.equals("SWAP")) {
						List<Switch> moves = stringToSwitchList(readmessage.nextLine());
						if (stackSize < moves.size() || !hasAllCardsSwap(moves)) {
							view.showMessage("Try again, stack size: " + stackSize);
							handleNext(arguments);
						} else {
							thisplayer.removeFromHandSwitch(moves);
							clienthandler.sendMessage(message);
							reader.close();
							readmessage.close();
						}
					} else {
						handleNext(arguments);
					}
				}
			} 
		}
	}
	
	/**
	 * Get's called by the method handleMessage() if it starts with NEW.
	 * This method handles the new tiles given by the server.
	 * @param arguments String to be decoded
	 */
	/*@ ensures this.getThisPlayer().getHand() != \old(this.getThisPlayer().getHand());*/
	private void handleNew(String arguments) {
		Scanner reader = new Scanner(arguments);
		while (reader.hasNext()) {
			String cardstring = reader.next();
			if (!cardstring.equals("empty")) {
				char[] cardchars = cardstring.toCharArray();
				synchronized (thisplayer) {
					try {
						thisplayer.getHand().add(new Card(cardchars[0], cardchars[1]));
					} catch (InvalidCharacterException e) {
						
					}
				}
			} else {
				view.showMessage("No new cards available");
			}
		}
		reader.close();
	}
	
	/**
	 * Get's called by the method handleMessage() if it starts with TURN.
	 * This method handles the output of the server that sends the turn of
	 * other players.
	 * @param arguments String to be decoded
	 */ 
	/*@ ensures arguments.length() == 10 ==> this.getBoard() == \old(this.getBoard());
	 	ensures arguments.length() != 10 ==> this.getBoard() != \old(this.getBoard());*/
	private void handleTurn(String arguments) {
		Scanner reader = new Scanner(arguments);
		Player player = getPlayer(Integer.parseInt(reader.next()));
		String word = reader.next();
		if (word.equals("empty")) {
			view.showMessage("Er is geruild");
		} else {
			List<Place> moves = stringToPlaceList(word + " " + reader.nextLine());
			if (stackSize > moves.size()) {
				stackSize -= moves.size();
			} else if (stackSize < moves.size()) {
				stackSize = 0;
			}
			player.updateScore(board.movePoints(moves));
			for (Place p: moves) {
				board.placeCard(p);
			}
			
		}
		setChanged();
		notifyObservers();
		view.showScore(player);
		reader.close();
	}
	
	/**
	 * Get's called by the method handleMessage() if it starts with WINNER.
	 * This method handles the output of the server that sends the winner 
	 * of the game.
	 * @param arguments String to be decoded
	 */ 
	/*@ ensures this.getGameEnd() == true;*/
	private void handleWinner(String arguments) {
		Scanner reader = new Scanner(arguments);
		int winner = Integer.parseInt(reader.next());
		view.showMessage("Player: " + getPlayer(winner).getName() + " won the game");
		reader.close();
		gameend = true;
		shutDown();
	}
	
	/**
	 * Get's called by the method handleMessage() if it starts with KICK.
	 * This method get everything sorted out when a player is kicked.
	 * @param arguments String to be decoded
	 */ 
	/*@ ensures stackSize > \old(stackSize);*/
	private void handleKick(String arguments) {
		Scanner reader = new Scanner(arguments);
		Player player = getPlayer(Integer.parseInt(reader.next()));
		int tilesBack = Integer.parseInt(reader.next());
		stackSize += tilesBack;
		String reason = reader.nextLine();
		if (player.equals(thisplayer)) {
			view.showKick(player, reason);
			view.showMessage("You got kicked!" + reason);
			reader.close();
			shutDown();
		}
		reader.close();
	}
	
	/**
	 * Checks if the players has all cards he wants to play.
	 * @param moves List to be checked
	 */ 
	/*@ ensures (\forall int i; 0 <= i & i < this.getThisPlayer().getHand().size(); 
	 				(\forall int j; 0 <= j & j < moves.size();
	 				this.getThisPlayer().getHand().get(i).getColor() == 
	 						moves.get(j).getCard().getColor() &&
	 				this.getThisPlayer().getHand().get(i).getFigure() == 
	 						moves.get(j).getCard().getFigure()) 
	 				==> \result == true);*/
	public Boolean hasAllCardsMove(List<Place> moves) {
		boolean result = true;
		List<Card> playedcards = new ArrayList<Card>();
		int i = 0;
		for (Place p: moves) {
			Card c = p.getCard();
			playedcards.add(c);
		}
	
		outer : for (Card c: playedcards) {
			for (Card chand: thisplayer.getHand()) {
				if (c.getColor().equals(chand.getColor()) && 
						  c.getFigure().equals(chand.getFigure())) {
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
	 * Checks if the players has all cards he wants to swap.
	 * @param moves List to be checked
	 */ 
	/*@ ensures (\forall int i; 0 <= i & i < this.getThisPlayer().getHand().size(); 
	 				(\forall int j; 0 <= j & j < moves.size();
	 				this.getThisPlayer().getHand().get(i).getColor() == 
	 						moves.get(j).getCard().getColor() &&
	 				this.getThisPlayer().getHand().get(i).getFigure() == 
	 						moves.get(j).getCard().getFigure()) 
	 				==> \result == true);*/
	public Boolean hasAllCardsSwap(List<Switch> moves) {
		boolean result = true;
		List<Card> playedcards = new ArrayList<Card>();
		int i = 0;
		for (Switch s: moves) {
			Card c = s.getCard();
			playedcards.add(c);
		}
	
		outer : for (Card c: playedcards) {
			for (Card chand: thisplayer.getHand()) {
				if (c.getColor().equals(chand.getColor()) && 
						  c.getFigure().equals(chand.getFigure())) {
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
	 * This methods converts a string with correctly formatted Place.
	 * to a List<Place>
	 * JML is including Spacebar and requires there to not be a space at the end.
	 * @param movestring
	 * @return List<Place>
	 */
	public List<Place> stringToPlaceList(String movestring) {
		Scanner reader = new Scanner(movestring);
		Scanner countreader = new Scanner(movestring);
		int i = 0;
		while (countreader.hasNext() && countreader.next() != null) {
			i++;
		}
		List<Place> moves = new ArrayList<Place>();
		if (i % 3 == 0) {
			while (reader.hasNext()) {
				String cardstring = reader.next();
				char[] cardchars = cardstring.toCharArray();
				if (cardchars.length != 2) {
					break;
				}
				try {
					Card card = new Card(cardchars[0], cardchars[1]);
					if (!reader.hasNext()) {
						break;
					}
					String y = reader.next();
					int ycoor = Integer.parseInt(y);
					
					if (!reader.hasNext()) {
						break;
					}
					String x = reader.next();
					int xcoor = Integer.parseInt(x);
					
					Place place = new Place(card, ycoor, xcoor);
					moves.add(place);
				} catch (InvalidCharacterException e) {
					moves = null;
				}
			}
		} else {
			moves = null;
		}
		countreader.close();
		reader.close();
		return moves;
	}
	
	/**
	 * This methods converts a string with correctly formatted Switch.
	 * to a List<Switch>
	 * JML is including Spacebar and requires there to not be a space at the end.
	 * @param movestring
	 * @return List<Swtich>
	 */
	/*@ requires (movestring.length() - 6) % 3 == 0;*/
	public List<Switch> stringToSwitchList(String movestring) {
		Scanner reader = new Scanner(movestring);
		List<Switch> moves = new ArrayList<Switch>();	
		while (reader.hasNext()) {
			String cardstring = reader.next();
			char[] cardchars = cardstring.toCharArray();
			if (cardchars.length != 2) {
				break;
			}
			try {
				Card card = new Card(cardchars[0], cardchars[1]);
				moves.add(new Switch(card));
				// catches an invalid card
			} catch (InvalidCharacterException e) {
				moves = null;
			}
			if (!reader.hasNext()) {
				break;
			}
		}
		reader.close();
		return moves;
	}
	
	/**
	 * Returns the player of which the playernumber is given.
	 * @param playernumber
	 * @return
	 */
	/*@pure*/public Player getPlayer(int playernumber) {
		Player result = null;
		if (getThisPlayer().getNumber() == playernumber) {
			result = thisplayer;
		} else {
			for (Player player: players) {
				if (player.getNumber() == playernumber) {
					result = player;
				}
			}
		}
		return result;
	}
	
	/*@pure*/public List<Player> getPlayers() {
		return players;
	}
	
	/*@pure*/public LocalPlayer getThisPlayer() {
		return thisplayer;
	}
	
	/*@pure*/public ClientHandler getClientHandler() {
		return clienthandler;
	}
	
	/*@pure*/public int getAIThinkTime() {
		return aithinktime;
	}
	
	/*@pure*/boolean completeMoveProcessed() {
		return completemoveprocessed;
	}
	
	/*@pure*/public int getPlayerNumber() {
		return thisplayer.getNumber();
	}
	
	/*@pure*/public Board getBoard() {
		return this.board;
	}
	
	/*@pure*/public TUIView getView() {
		return view;
	}
	
	/*@pure*/public int getStackSize() {
		return stackSize;
	}
	
	/*@pure*/public boolean getGameEnd() {
		return gameend;
	}
	
	public void shutDown() {
		clienthandler.stopConnection();
		System.exit(0);
	}
}