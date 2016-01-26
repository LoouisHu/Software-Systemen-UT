
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

    /** Starts a Server-application. 
     * @throws IOException */
    public static void main(String[] args) throws IOException {
    	if(args.length != 2){
    		System.out.print(USAGE);
    		System.exit(0);
    	}
    	// parse args[1] - the port
    	String name = args[0];
    	int port = 0;
    	ServerSocket serverSocket;
    	Socket sock;
    	
    	try {
    		port = Integer.parseInt(args[1]);
    	} catch (NumberFormatException e){
    		System.err.println(e);
    	}
    	
    	class ClientHandler extends Thread{
    		private String name;
    		private Socket sock;
    		
    		public ClientHandler(String name, Socket sock){
    			this.name = name;
    			this.sock = sock;
    		}
    		public void run(){
    			try {
    				Peer server = new Peer(name, sock);
    				Thread streamInputHandler = new Thread(server);
    			streamInputHandler.start();
    			server.handleTerminalInput();
    			server.shutDown();
    			} catch (IOException e){
    				e.printStackTrace();
    			}
    		}
    	}
    }

} // end of class Server
