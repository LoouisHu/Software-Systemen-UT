package Controller;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.net.Socket;

public class Client implements Runnable{
	private String  name;
	private Socket sock;
	private DataInputStream in;
	private DataOutputStream out;
	
	public Client (String name, InetAddress addr, int port){
		this.name = name;
		sock = new Socket(addr, port);
		in = new DataInputStream(sock.getInputStream());
		out = new DataOutputStream(sock.getOutputStream());
	
		
	}
	
	@Override
	public void run() {
		// TODO Auto-generated method stub
	}

}
