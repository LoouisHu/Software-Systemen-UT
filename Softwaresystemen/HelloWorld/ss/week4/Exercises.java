package ss.week4;

public class Exercises {
	public static int countNegativeNumbers(int[] arr) {
    	int i = 0;
    	int k = 0;
    	while (i < arr.length -1){
    		if (i < 0){
    			k++;
    			i++;
    		}
    	return k;
    	}
    	
    }

    public static void reverseArray(int[] ints) {
    	int i = 0;
    	
    	
    }

    class SimpleList {
        public class Element {}

        public class Node {
            public Node next;
            public Element element;
        }

        private Node first;

        private Node find(Element element) {
            Node p = first;
            if (p == null) {
                return null;
            }
            while (p.next != null && !p.next.element.equals(element)) {
                p = p.next;
            }
            if (p.next == null) {
                return null;
            } else {
                return p;
            }
        }

        public void remove(Element element) {
            Node p = find(element);
            if (p != null) {
                p.next = p.next.next;
            }
        }
    }
}
