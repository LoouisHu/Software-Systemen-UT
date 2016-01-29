package controller;

import model.Board;
import model.Tile;
import model.TileBag;
import model.Move;
import player.SocketPlayer;
import model.Coord;
import player.Player;
import java.util.*;
import view.TUI;

public class Server extends Thread {
	public static final String USAGE = 
			  "usage: " + Server.class.getName() + "<port>" + " <aithinktime>";
	/*@ invariant getThreads().size() <= 4;
	 	invariant getStack().stackAmount() <= 108;*/
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
	 * Constructs a new server object with a control object think time and a View.
	 * @param controller
	 * @param thinktime
	 * @param ui
	 */
	public Server(ServerController controller, int thinktime, TUIView ui) {
		this.view = ui;
		aithinktime = thinktime;
		this.controller = controller;
	}
	
	/**
	 * Run methods creates a new game by calling the method creatGame(). 
	 * After the game is created the game is started with an equal naming.
	 * While the game should keep going this happens, when it shouldn't be
	 * the winner is determined and the server is shutdown.
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
	 * This message handles all commands and redirects them to the corresponding methods.
	 * @param ch
	 * @param msg
	 */
	public void handleMessage(ClientHandler ch, String msg) {
		view.showMessage("[TO SERVER] : " + msg);
		Scanner reader = new Scanner(msg);
		String command = reader.next();
		if (command.equals("HELLO") && reader.hasNext()) {
			handleHello(reader.next(), ch);
		} else if (command.equals("MOVE") && reader.hasNext()) {
			handleMove(reader.nextLine(), ch);
		} else if (command.equals("SWAP") && reader.hasNext()) {
			handleSwap(reader.nextLine(), ch);
		} else if (command.equals("START")) {
			this.start();
		}
		
		reader.close();
	}
		
	/**
	 * Returns the number of players.
	 * @return int
	 */
	/*@ ensures \result == getThreads().size();
	/*@pure*/public int getNoOfPlayers() {
		return threads.size();
	}
	
	/**
	 * Returns the player.
	 * @param playerno the number assigned by the server to a player.
	 * @return the players which the number is assigned too.
	 */
	/*@ requires playerno < 4;
	    ensures \result == getThreads().get(playerno).getPlayer();*/
	public NetworkPlayer getPlayer(int playerno) {
		return threads.get(playerno).getPlayer();
	}
	
	/**
	 * Adds a client to the list threads. A client has a player. 
	 * In this way players are connected to a server.
	 * @param c
	 */
	/*@ ensures getThreads().contains(c);*/
	public void addClient(ClientHandler c) {
		threads.add(c);
	}
	
	
	/**
	 * Starts the game.
	 * Broadcasts all the players + no and as a last integer the aithinktime.
	 * Sends a complete hand of six cards to all players.
	 * Determines and send the first player to play cards, done so by dertermineFirstTurn().
	 */
	/*@ ensures (\forall int i; 0 <= i & i < getThreads().size();
	 					getThreads().get(i).getPlayer().getHand().size() == 6);*/
	public void startGame() {
		String command = "NAMES"; 
		for (ClientHandler ch: threads) {
			command = command + " " + ch.getPlayer().getName() + " " + ch.getPlayer().getNumber();
		}
		command = command + " " + aithinktime;
		
		broadcast(command);
		
		try {
			for (ClientHandler ch: threads) {
				List<Card> newcards = stack.drawCards(6);
				ch.getPlayer().setHand(newcards);
				System.out.println("[FROM SERVER TO " + ch.getPlayer().getName() + "] : " 
						  + giveCardsString(newcards));
				ch.sendMessage(giveCardsString(newcards));
			}
		} catch (NotEnoughTilesException e) {
			
		}
		playerturn = determineFirstTurn(threads);
		broadcast("NEXT " + determineFirstTurn(threads));
	}
	
	/**
	 * Checks if there is more then one/zero player in the game.
	 * Checks if the hand of the player who just played is empty. 
	 * If the first check passes and the hand is not empty the next player is send.
	 */
	/*@ ensures getThreads().size() > 1 ==> 
	 				getPlayerturn() == (getPlayerturn() + 1) % getThreads().size();*/
	public void nextTurn() {
		System.out.println(board.toString());
		System.out.println("Stack size: " + stack.stackAmount());
		if (threads.size() == 1) {
			Player player = threads.get(0).getPlayer();
			broadcast("WINNER " + player.getNumber());
		} else if (threads.size() == 0) {
			shutDown();
		} else if (getPlayer(playerturn).getHand().size() == 0 && stack.stackAmount() == 0) {
			getPlayer(playerturn).updateScore(6);
			gameOver();
		} else if (!noValidMoveAvailable(getClientHandler(getPlayer(playerturn))) && 
				  stack.stackAmount() == 0) {
			broadcast("NEXT " + getPlayer(playerturn).getNumber());
		} else {
			playerturn = (playerturn + 1) % threads.size();
			if (getPlayer(playerturn) == null) {
				nextTurn();
			}
		}
		broadcast("NEXT " + getPlayer(playerturn).getNumber());
	}
	
	/**
	 * Checks if the game is over, if players is 1, the stack and player hand is 0, 
	 * or there are no valid moves anymore the game is over.
	 * @param ch
	 * @return
	 */
	/*@ ensures getThreads().size() == 1 ==> \result == true;
	    ensures this.getStack().stackAmount() == 0 ==> \result == false;*/
	public boolean gameOver() {
		boolean result = false;
		if (threads.size() == 1) {
			result = true;
		} else if (stack.stackAmount() == 0) {
			for (ClientHandler ch: threads) {
				if (!noValidMoveAvailable(ch)) {
					result = false;
				}
			}
		} 
		return result;
	}

	/**
	 * Sends a message too all the clients.
	 * @param msg
	 */
	/*@ requires msg != null;
	 	requires getThreads().size() > 0;*/
	public void broadcast(String msg) {
		System.out.println("[FROM SERVER] : " + msg);
		for (ClientHandler ch: threads) {
			ch.sendMessage(msg);
		}
	}
	
	/**
	 * Checks if a valid name was entered, adds the name to the connected networkplayer
	 * gives this player a number sends the welcome message to the player 
	 * kicks if the name is not valid
	 * @param message
	 * @param ch
	 */
	/*@ signals (Exception e) e instanceof InValidNameException <==> !validName(message);
	*/
	//needs to have a message and a clienthandler
	public void handleHello(String message, ClientHandler ch) {
		try {
			if (validName(message)) {
				ch.getPlayer().setName(message);
				ch.getPlayer().setNumber(playernumber);
				playernumber += 1;
				String response = "WELCOME " + ch.getPlayer().getName() + 
						  " " + ch.getPlayer().getNumber();
				System.out.println("[FROM SERVER TO " + ch.getPlayer().getName() 
						  + "] : " + response);
				ch.sendMessage(response);
			}
		} catch (InValidNameException e) {
			kickPlayer(ch, "This name was not valid");
		}
	}
	
	/**
	 * Handles a move command. Checks if it was the player's turn and if there is a message
	 * Creates a list of moves from the message
	 * checks if a complete move was processed and if the player has all 
	 * the cards he tried to play
	 * @param message
	 * @param ch
	 */
	/*@ requires this.getThreads().contains(ch);
	 */
	public void handleMove(String message, ClientHandler ch) {
		Scanner reader = new Scanner(message);
		boolean completeMoveProcessed = false;
		// Checks if it is the players turn and if there are commands
		if (ch.getPlayer().getNumber() == playerturn && reader.hasNext()) {
			try { 
				List<Place> moves = new ArrayList<Place>();
				while (reader.hasNext()) {
					completeMoveProcessed = false;
					String cardstring = reader.next();
					char[] cardchars = cardstring.toCharArray();
					// If there are not enough charachters, stop.
					if (cardchars.length != 2) {
						break;
					}
					try {
						Card card = new Card(cardchars[0], cardchars[1]);
						
						// If there is nothing after the card stop.
						if (!reader.hasNext()) {
							break;
						}
						String y = reader.next();
						int ycoor = Integer.parseInt(y);
						
						// If there is no x coordinate stop.
						if (!reader.hasNext()) {
							break;
						}
						String x = reader.next();
						int xcoor = Integer.parseInt(x);
						
						//If everything is correct make a new card add it to the list en 
						Place place = new Place(card, ycoor, xcoor);
						moves.add(place);
						completeMoveProcessed = true;
					} catch (InvalidCharacterException e) {
						kickPlayer(ch, e.getMessage());
					}
				}
				// If there was atleast one correct formatted move do this
				if (completeMoveProcessed && !moves.isEmpty()) {
					try {
						if (hasAllCardsMove(ch, moves) && board.isValidMoveList(moves)) {
							// Cards need to be placed for score
							for (Place p: moves) {
								board.placeCard(p);
							}
								/*
								 * updates the score of this player
								 * draws new cards from the stack
								 * removes the cards he played from his hand, 
								 * sends him a message with the new cards
								 * broadcasts a message to all players with the turn
								 */
							ch.getPlayer().updateScore(board.movePoints(moves));
							// Score removes cards place them.
							for (Place p: moves) {
								board.placeCard(p);
							}
							
							if (stack.stackAmount() > 0) {
								List<Card> newcards = stack.drawCards(moves.size());
								ch.getPlayer().placeCards(moves, newcards);
								System.out.println("[FROM SERVER TO " + ch.getPlayer().getName() 
										  + "] : " + giveCardsString(newcards));
								ch.sendMessage(giveCardsString(newcards));
								String turnstring = "TURN " + ch.getPlayer().getNumber();
								for (Place p: moves) {
									turnstring = turnstring + p.toString();
								}
								broadcast(turnstring);
							} else {
								ch.getPlayer().removeFromHandPlaces(moves);
								System.out.println("[FROM SERVER TO " + ch.getPlayer().getName() 
										  + "] : NEW empty");
								ch.sendMessage("NEW empty");
								String turnstring = "TURN " + ch.getPlayer().getNumber();
								for (Place p: moves) {
									turnstring = turnstring + p.toString();
								}
								broadcast(turnstring);
								
							}
						}
					} catch (NotEnoughTilesException e) {
						ch.getPlayer().removeFromHandPlaces(moves);
						ch.sendMessage("NEW empty");
					}
				}
			} catch (LoneSpotException | NoEmptySpotException | NoValidCombinationException
					| LineTooLongException e) {
				kickPlayer(ch, "This was not a valid move");
				e.printStackTrace();
			} catch (NumberFormatException e) {
				kickPlayer(ch, "Not a valid move command");
			} finally {
				nextTurn();
				reader.close();
			}
		}
	}
	
	/**
	 * Handles a swap command.
	 * checks if it was his turn and if there is a message
	 * Creates a list of moves from the message
	 * @param message
	 * @param ch
	 */
	public void handleSwap(String message, ClientHandler ch) {
		Scanner reader = new Scanner(message);
		if (ch.getPlayer().getNumber() == playerturn && reader.hasNext()) {
			try {
				List<Move> moves = new ArrayList<Move>();	
				while (reader.hasNext()) {
					String cardstring = reader.next();
					char[] cardchars = cardstring.toCharArray();
					if (cardchars.length != 2) {
						kickPlayer(ch, "Nice try, but a card only has 2 chars");
						break;
					}
					try {
						Card card = new Card(cardchars[0], cardchars[1]);
						moves.add(new Switch(card));
						// catches an invalid card
					} catch (InvalidCharacterException e) {
						e.printStackTrace();
						kickPlayer(ch, "One of the characters was not valid");
					}
					if (!reader.hasNext()) {
						break;
					}
				}
				// If the player tried to swap to an empty stack, kick him
				if (stack.stackAmount() < moves.size()) {
					kickPlayer(ch, "U should have checked the stack before");
				} else if (hasAllCardsSwap(ch, moves)) {
					try {
						/*
						 * Draws new cards from the stack
						 * swaps these cards with the hand of the player
						 * sends him a message with the new cards
						 * broadcasts the turn
						 */
						List<Card> newcards = stack.swapToStack(moves);
						ch.getPlayer().swapHand(moves, newcards);
						ch.sendMessage(giveCardsString(newcards));
						broadcast("TURN" + " " + ch.getPlayer().getNumber() + " empty");
					} catch (NotEnoughTilesException e) {
						kickPlayer(ch, "Nice try, but the stack was empty");
					}
				} else {
					kickPlayer(ch, "U did not have these cards");
				}
			} finally {
				reader.close();
				nextTurn();
			}
		} else {
			kickPlayer(ch, "That was not a valid swap");
		}
	}
	
	/**
	 * creates a string of cards from a list of cards.
	 * @param cardlist
	 * @return
	 */
	public String giveCardsString(List<Card> cardlist) {
		String result = "NEW";
		if (stack.stackAmount() == 0) {
			result = result + " empty";
		} else {
			for (Card c: cardlist) {
				result = result + " " + c.cardToChar();
			}
		}
		return result;
	}
	
	/**
	 * Checks if a player has all the cards he tries to play.
	 * @param ch
	 * @param moves List <Place>
	 * @return
	 */
	public Boolean hasAllCardsMove(ClientHandler ch, List<Place> moves) {
		boolean result = true;
		List<Card> playedcards = new ArrayList<Card>();
		int i = 0;
		for (Place p: moves) {
			Card c = p.getCard();
			playedcards.add(c);
		}
	
		outer : for (Card c: playedcards) {
			for (Card chand: ch.getPlayer().getHand()) {
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
	 * Checks if a player has all the cards he tries to play.
	 * @param ch
	 * @param moves List <Move>
	 * @return
	 */
	public Boolean hasAllCardsSwap(ClientHandler ch, List<Move> moves) {
		boolean result = true;
		List<Card> playedcards = new ArrayList<Card>();
		int i = 0;
		for (Move s: moves) {
			Card c = s.getCard();
			playedcards.add(c);
		}
	
		outer : for (Card c: playedcards) {
			for (Card chand: ch.getPlayer().getHand()) {
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
	 * Checks if a player has a move left.
	 * It goes through all the possibilities and checks if there is atleast one.
	 * @param ch ClientHandler
	 * @return
	 */
	/*@ ensures (\forall int i, j, k; 0 <= i & i < 183 
				  & 0 <= k & k <= 183 & 0 <= j & j < ch.getPlayer().getHand().size();
				  this.getBoard().isValidMove(new Place(ch.getPlayer().getHand().get(i), i, k)) 
				  ==> \result == true); 
	 */
	public boolean noValidMoveAvailable(ClientHandler ch) { 
		boolean result = true;
		if (ch.getPlayer().getHand().size() == 0) {
			result = true;
		} else {
			for (int i = 0; i < ch.getPlayer().getHand().size(); i++) {
				for (int y = 0; y < 183; y++) {
					for (int x = 0; x < 183; x++) {
						Place move = new Place(ch.getPlayer().getHand().get(i), x, y);
						try {
							if (board.isValidMove(move)) {
								result = false;
								break;
							}
						} catch (LoneSpotException | NoValidCombinationException
								| LineTooLongException e) {
						}
					}
				}
			}
		}
		return result;
	}
	
	/**
	 * Calculates the max score for each player's first turn .
	 * returns the number of the player that had the highest score and goes first
	 * @param handlerlist
	 * @return
	 */
	public int determineFirstTurn(List<ClientHandler> handlerlist) {
		Map<Integer, Integer> playerscores = new HashMap<Integer, Integer>();
		int[] score = new int[12];
		int result = 0;
		for (ClientHandler ch: handlerlist) {
			int maxscore = 0;
			for (Card c: ch.getPlayer().getHand()) {
				switch (c.getColor()) {
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
				switch (c.getFigure()) {
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
					case CLUB: 
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
		for (ClientHandler ch: threads) {
			if (ch.getPlayer().getScore() > highscore) {
				highscore = ch.getPlayer().getScore();
				winnernumber = ch.getPlayer().getNumber();
			}
		}
		broadcast("WINNER " + winnernumber);
		shutDown();
	}
	
	
	
	/**
	 * Handles a player kick.
	 * Sends a message to all the client with the amount of cards returned to the stack
	 * and add the cards to the stack.
	 * @param ch
	 * @param reason
	 */
	public void kickPlayer(ClientHandler ch, String reason) {
		List<Card> hand = ch.getPlayer().getHand();
		if (hand != null) {
			for (Card c: hand) {
				stack.addCard(c);
			}
		}
		broadcast("KICK " + ch.getPlayer().getNumber() + " " + hand.size() + " " + reason);
		if (playerturn == ch.getPlayer().getNumber()) {
			nextTurn();
		}
		threads.remove(ch);
	}
	
	/**
	 * Creates a new game environment.
	 */
	public void createGame() {
		board = new Board();
		stack = new CardStack();
	}
	
	/**
	 * Closes all the connections and finnaly the server.
	 */
	public void shutDown() {
		for (int i = 0; i < threads.size(); i++) {
			threads.get(i).stopConnection();
		}
		this.interrupt();
	}
	
	/*@ ensures name.matches("[a-zA-Z]+");*/;
	/*@pure*/public static boolean validName(String name) throws InValidNameException {
		boolean result = true;
		
		char[] letters = name.toCharArray();
		
		for (char l : letters) {
			if (!Character.isLetter(l)) {			
				throw new InValidNameException("Not a valid name");
			}
		}
		return result;
	}
	
	public ClientHandler getClientHandler(Player player) {
		ClientHandler found = null;
		for (ClientHandler ch: threads) {
			if (ch.getPlayer() == player) {
				found = ch;
			}
		}
		return found;
	}
	
	/*@pure*/public List<ClientHandler> getThreads() {
		return threads;
	}
	
	/*@pure*/public int getPlayerturn() {
		return playerturn;
	}
	
	/*@pure*/public CardStack getStack() {
		return stack;
	}
	
	/*@pure*/public Board getBoard() {
		return board;
	}
	
	/*@pure*/public ServerController getController() {
		return controller;
	}
	
}
