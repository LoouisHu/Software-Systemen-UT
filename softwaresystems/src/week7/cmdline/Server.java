
package week7.cmdline;

import java.io.IOException;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.UnknownHostException;

/**
 * Server. 
 * @author  Theo Ruys
 * @version 2005.02.21
 */
public class Server {
    private static final String USAGE
        = "usage: " + Server.class.getName() + " <name> <port>";

    /** Starts a Server-application. */
    public static void main(String[] args) {
    	if (args.length != 2) {
    		System.out.println(USAGE);
    		System.exit(0);
    	}
    	
    	ServerSocket serverSocket = null;
    	try {
    		int port = Integer.parseInt(args[1]);
    		serverSocket = new ServerSocket(port);
    		Peer peer;
    		while (true) {
    			Socket sock = serverSocket.accept();
    			(new ClientHandler(args[0], sock)).start();
    		}
    	} catch (IOException e) {
    		System.out.println(e.getMessage());
    	} finally {
    		try {
    			serverSocket.close();
    		} catch (IOException e) {
    			System.out.println(e.getMessage());
    		}
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
