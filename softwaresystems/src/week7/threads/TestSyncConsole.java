package week7.threads;

public class TestSyncConsole extends Thread {

	private String name;
	
	public TestSyncConsole(String name) {
		this.name = name;
	}
	
	synchronized private void sum() {
		int num1 = SyncConsole.readInt(name + " :: Give int 1: ");
		int num2 = SyncConsole.readInt(name + " :: Give int 2: ");
		SyncConsole.println(name + " :: " + num1 + " + " + num2 + " = " + (num1+num2));
	}

}
