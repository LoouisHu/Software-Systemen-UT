package controller;
import java.util.*;

import view.TUIView;

public class ServerController extends Thread {
	
	Connect connect;
	List<Server> serverlist;
	TUIView view;
	int aithinktime;
	public static final String USAGE = 
			  "usage: " + Server.class.getName() + "<port>" + " <aithinktime>";
	
	public static void main(String[] args) {
		if (args.length != 2) {
			System.out.println(USAGE);
			System.exit(0);
		}
		
		new ServerController(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
	}
	
	//---Constructor---
	/**
	 * Constructs a ServerController with an AIThinkTime and a port.
	 * @param portArg
	 * @param aiThinkTimearg
	 */
	public ServerController(int portArg,  int aiThinkTimearg) {
		aithinktime = aiThinkTimearg;
		view = new TUIView(this);
		serverlist = new ArrayList<Server>();
		Server server = new Server(this, aithinktime, view);
		serverlist.add(server);
		connect = new Connect(server, portArg, view);
		this.start();
			
	}
	
	//---Commands---
	public void nextGame() {
		(serverlist.get(serverlist.size() - 1)).start();
		Server server = new Server(this, aithinktime, view);
		serverlist.add(server);
	}	
	
	public void handleInput(String command) {
		if (command.equals("start")) {
			nextGame();
		} else {
			view.showMessage(command + " could not be resolved to a command");
		}
	}
	
	//---Run---	
	public void run() {
		while (true) {
			String command = view.getCommand();
			handleInput(command);	
		}
	}
}
