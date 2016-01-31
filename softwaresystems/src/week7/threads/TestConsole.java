package week7.threads;

public class TestConsole extends Thread {

	@Override
	public void run() {
		int i1, i2;
		i1 = Console.readInt(this.getName() + ": No. 1\n");
		i2 = Console.readInt(this.getName() + ": No. 2\n");
		Console.println(this.getName() + ": " + i1 + " + " + i2 + " = " + (i1 + i2));
	}

	public static void main(String[] args) {
		TestConsole t1 = new TestConsole();
		TestConsole t2 = new TestConsole();
		t1.start();
		t2.start();
	}
}
