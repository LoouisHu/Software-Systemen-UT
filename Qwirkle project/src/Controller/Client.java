package Controller;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.net.Socket;
import java.util.Observable;

import Qwirkle.*;
import player.*;
import view.*;

public class Client extends Observable{
	
	private int aiThinkTime;
	private UI ui;
	public Connection conn;
	public LocalPlayer player;
	private List<Player> opponents = new ArrayList<Player>();
	public Board board;
	private List<Block> tempHand = new ArrayList<Block>();
	private int stackSize;
	private int numberOfPlayers = opponents.size() + 1;
	
	
	public Client(UI uiArg, Socket sockArg, LocalPlayer player) {
		board = new Board();
		ui = uiArg;
		this.player = player;
		ui.setClient(this);
		conn = new Connection(this, sockArg);
		this.addObserver(ui);
		conn.sendString("HELLO " + player.getName());
	}
	
	public void run() {
		// TODO Auto-generated method stub
	}

}
