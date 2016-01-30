package controller;
import java.util.*;
import view.TUI;

public class ServerController extends Thread {
	
	Connect connect;
	List<Server> serverlist;
	TUI view;
	int aithinktime;
	public static final String USAGE = 
			  "usage: " + Server.class.getName() + "<port>" + " <aithinktime>";
	
	public void run() {
		while (true) {
			String command = view.getCommand();
			handleInput(command);	
		}
	}

	/**
	 * Constructs a ServerController with an AIThinkTime and a port.
	 * @param portArg
	 * @param aiThinkTimearg
	 */
	public ServerController(int portArg,  int aiThinkTimearg) {
		aithinktime = aiThinkTimearg;
		view = new TUI(this);
		serverlist = new ArrayList<Server>();
		Server server = new Server(this, aithinktime, view);
		serverlist.add(server);
		connect = new Connect(server, portArg, view);
		this.start();
			
	}
	
	public void handleInput(String command) {
		if (command.equals("start")) {
			nextGame();
		} else {
			view.displayMessage(command + " This is not a command. Try again.");
		}
	}

	public void nextGame() {
		(serverlist.get(serverlist.size() - 1)).start();
		Server server = new Server(this, aithinktime, view);
		serverlist.add(server);
	}	
	
	public static void main(String[] args) {
		if (args.length != 2) {
			System.out.println(USAGE);
			System.exit(0);
		}
		
		new ServerController(Integer.parseInt(args[0]), Integer.parseInt(args[1]));
	}
}
