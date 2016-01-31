package week7.bounce;

class AnimateThread extends Thread {

	private BallPanel bp;

	AnimateThread(BallPanel bpArg) {
		this.bp = bpArg;
	}

	public void run() {
		bp.animate();
	}

}
