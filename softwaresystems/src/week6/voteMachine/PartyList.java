package week6.voteMachine;

import java.util.*;

public class PartyList extends Observable {
	
	private List<String> parties = new ArrayList<String>();
	
	public PartyList() {
		// TODO Auto-generated constructor stub
		
	}
	
	public List<String> getParties(){
		return parties;
	}

	public void addParty(String partyname){
		if (!hasParty(partyname)){
			parties.add(partyname);
			setChanged();
			notifyObservers("party");
		}
	}
	
	public boolean hasParty(String party) {
		return parties.contains(party);
	}
	
	
	
}
