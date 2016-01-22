package Controller;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.Socket;

import Qwirkle.Board;

public class PlayerHandler implements Runnable{
	private Socket soc;
	private Board board;
	
	BufferedReader in;
	
	public PlayerHandler(Socket soc, Board board) {
		this.soc = soc;
		this.board = board;
	}
	
	public void run(){
		
		try {
			in = new BufferedReader(new InputStreamReader(soc.getInputStream()));
			String lline;
			while((lline = in.readLine()) != null){
				//implement commands to be read;
				//implement commands to be send?;
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		
	}
	
	

}
