package player;

import java.util.Set;

import Qwirkle.Tile;

public class ComputerPlayer extends Player {
	
	private Strategy strat;

	public ComputerPlayer(String name, Set<Tile> hand) {
		super(name, hand);
		// TODO Auto-generated constructor stub
	}
	
	public ComputerPlayer(String name, Set<Tile> hand, Strategy strat){
		super(name, hand);
		this.strat = strat;
	}

}
