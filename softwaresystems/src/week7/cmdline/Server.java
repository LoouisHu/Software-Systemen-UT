
package week7.cmdline;

import java.io.IOException;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.UnknownHostException;

/**
 * Server.
 * 
 * @author Theo Ruys
 * @version 2005.02.21
 */
public class Server {
	private static final String USAGE = "usage: " + Server.class.getName() + " <name> <port>";

	/** Starts a Server-application. */
	public static void main(String[] args) {
		if (args.length != 2) {
			System.out.println(USAGE);
			System.exit(0);
		}
		int port = 0;
		ServerSocket serverSocket = null;
		Socket sock = null;
		try {
			port = Integer.parseInt(args[1]);
		} catch (NumberFormatException e) {
			System.out.println(USAGE);
			System.exit(0);
		}

		try {
			serverSocket = new ServerSocket(port);
		} catch (IOException e1) {
			System.out.println("Kan de socket niet starten op deze port: " + port);
			System.exit(0);
		}
		try {
			sock = serverSocket.accept();
		} catch (IOException e) {
			System.out.println("K");
		}
		try {
			Peer peer = new Peer(args[0], sock);
			Thread t = new Thread(peer);
			t.start();
			peer.handleTerminalInput();
			peer.shutDown();
		} catch (IOException e) {
			System.out.println("Appel is beter dan peer");
		}
	}

	private static class ClientHandler extends Thread {
		private String name;
		private Socket sock;

		public ClientHandler(String name, Socket sock) {
			this.name = name;
			this.sock = sock;
		}

		public void run() {
			try {
				Peer server = new Peer(name, sock);
				Thread streamInputHandler = new Thread(server);
				streamInputHandler.start();
				server.handleTerminalInput();
				server.shutDown();
			} catch (IOException e) {
				e.printStackTrace();
			}

		}

	}

}
