package week6.voteMachine;

import java.util.*;

public class VoteList extends Observable {

	private Map<String, Integer> votes;

	public VoteList() {
		votes = new HashMap<String, Integer>();
	}

	public void addVote(String party) {
		int initial = 0;
		if (votes.containsKey(party)) {
			initial = votes.get(party);
		}
		votes.put(party, initial + 1);
		setChanged();
		notifyObservers("vote");
	}

	public Map<String, Integer> getVotes() {
		return votes;
	}
}