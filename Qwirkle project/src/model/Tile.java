package model;

public class Tile {

	public static enum Color {
		RED, ORANGE, BLUE, YELLOW, GREEN, PURPLE;
	}

	public static enum Shape {
		CIRCLE, DIAMOND, SQUARE, CLOVER, CROSS, STAR;
	}
	
	private Shape shape;
	private Color color;
	
	public Tile(Color color, Shape shape){
		this.shape = shape;
		this.color = color;
	}

	public Tile(char color, char shape){
		switch (color) {
		case 'R': this.color = Color.RED;
			break;
		case 'O': this.color = Color.ORANGE;
			break;
		case 'B': this.color = Color.BLUE;
			break;
		case 'Y': this.color = Color.YELLOW;
			break;
		case 'G': this.color = Color.GREEN;
			break;
		case 'P': this.color = Color.PURPLE;
			break;
		}
		
		switch(shape) {
		case 'o': this.shape = Shape.CIRCLE;
			break;
		case 'd': this.shape = Shape.DIAMOND;
			break;
		case 's': this.shape = Shape.SQUARE;
			break;
		case 'c': this.shape = Shape.CLOVER;
			break;
		case 'x': this.shape = Shape.CROSS;
			break;
		case '*': this.shape = Shape.STAR;
		}
	}
	/*pure*/
	public Color getColor(){
		 return color;
	}
	/*pure*/
	public Shape getShape(){
		return shape;
	}
	
	public String toString(){
		String result = "";
		switch (this.getColor()) {
		case RED: result = result.concat("R");
			break;
		case ORANGE: result = result.concat("O");
			break;
		case BLUE: result = result.concat("B");
			break;
		case YELLOW: result = result.concat("Y");
			break;
		case GREEN: result = result.concat("G");
			break;
		case PURPLE: result = result.concat("P");
			break;
		default: result.concat("@");
		}
		
		switch (this.getShape()) {
		case CIRCLE: result = result.concat("o");
			break;
		case DIAMOND: result = result.concat("d");
			break;
		case SQUARE: result = result.concat("s");
			break;
		case CLOVER: result = result.concat("c");
			break;
		case CROSS: result = result.concat("x");
			break;
		case STAR: result = result.concat("*");
			break;
		default: result.concat("@");
		}
		
		return result;
	}
	
}
