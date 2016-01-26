package week7.cmdline;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;

/**
 * Peer for a simple client-server application
 * @author  Theo Ruys
 * @version 2005.02.21
 */
public class Peer implements Runnable {
    public static final String EXIT = "exit";

    protected String name;
    protected Socket sock;
    protected BufferedReader in;
    protected BufferedWriter out;


    /*@
       requires (nameArg != null) && (sockArg != null);
     */
    /**
     * Constructor. creates a peer object based in the given parameters.
     * @param   nameArg name of the Peer-proces
     * @param   sockArg Socket of the Peer-proces
     */
    public Peer(String nameArg, Socket sockArg) throws IOException
    {
    	nameArg = name;
    	sockArg = sock;
    	//create input reader
    	in = new BufferedReader(new InputStreamReader(sockArg.getInputStream()));
    	//create output writer
    	out = new BufferedWriter(new OutputStreamWriter(sockArg.getOutputStream()));
    		
    }

    /**
     * Reads strings of the stream of the socket-connection and
     * writes the characters to the default output.
     */
    public void run() {
    	String theLine;
    	try{
    	while((theLine = in.readLine()) != null){
    		System.out.println(theLine);}
    	} catch (IOException e){
    		System.out.print(e);
    	}
    	
    }


    /**
     * Reads a string from the console and sends this string over
     * the socket-connection to the Peer process.
     * On Peer.EXIT the method ends
     */
    public void handleTerminalInput() {
    	boolean notEnded = true;
    	while (notEnded){
    		String line = "";
    		if (line.equals("Peer.EXIT")){
    			notEnded = false;
    		} else {
    			try {
    				out.write("[" + name + "]" + line);
    				out.newLine();
    				out.flush();
    			} catch (IOException e){
    				System.err.println(e);
    			}
    		}
    	}
    	
    }

    /**
     * Closes the connection, the sockets will be terminated
     */
    public void shutDown() {
    	try {
    		out.close();
    		in.close();
    		sock.close();;
    	} catch (IOException e){
    		System.err.println(e);
    	}
    }

    /**  returns name of the peer object*/
    public String getName() {
        return name;
    }

    /** read a line from the default input */
    static public String readString(String tekst) {
        System.out.print(tekst);
        String antw = null;
        try {
            BufferedReader in = new BufferedReader(new InputStreamReader(
                    System.in));
            antw = in.readLine();
        } catch (IOException e) {
        }

        return (antw == null) ? "" : antw;
    }
}
