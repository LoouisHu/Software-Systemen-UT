package ss.week4;

public class LinkedList<Element> {

    private /*@ spec_public @*/ int size;
    private Node first;

    //@ ensures \result.size == 0;
    public LinkedList () {
        size = 0;
        first = null;
    }

    public void add(int index, Element element) {
        Node newNode = new Node(element);
        if (index == 0) {
            newNode.next = first;
            first = newNode;
        } else {
            Node p = getNode(index-1);
            newNode.next = p.next;
            p.next = newNode;
        }
        size = size + 1;
    }

    //@ ensures this.size == \old(size) - 1;
    public void remove(Element element) {
        // TODO: implement, see exercise P-4.18
    	// Als er iets zit in de index, doe deze deze if statement.
    	if (element != null){
    		// Maak een findBefore instantie aan van Node
    		// Dit ding zoekt dus de next van de genoemde element ([] NEXT-> [element]
    		Node p = findBefore(element);
    		//De grootte van de lijst wordt met één kleiner, want we verwijderen wat, 't zou raar zijn als de lijst niet korter werd
    		size = size - 1;
    		//Als de p null geeft, dat betekent dat er geen NEXT van het gezochte element bestaat. De enige
    		//Node die dat heeft, is de eerste Node, wat er bestaat geen -1 index die een NEXT heeft naar index 0.
    		if(p == null){
    			//De first (null) wordt toegekend aan de eerste node.
    			first = getNode(1);
    		// Als de p.next wel bestaat en de p.next.next ook:
    		}else if(p.next != null && p.next.next != null ){
    			//Dan sla je een node van de verwijderde element over, want de p.next.next is de volgende element.
    			p.next = p.next.next;
    		}else{
    			p.next = null;
    		}
    		
    	}
    	
    }

    public Node findBefore(Element element) {
        // TODO: implement, see exercise P-4.18
    	// for loop dat alle indexi doorloopt
    	for (int i=0; i< this.size(); i++){
    		//De next van de node mag niet null zijn, de element van de next moet gelijk zijn met de element van findBefore()
			if (getNode(i).next != null && this.getNode(i).next.getElement() == element ){
				//Het returnt de Node waarvoor geld dat de element van die node hetzelfde is als de gegeven methode waar een element wordt opgeroepen (zoals remove(Element element))
				return getNode(i);
			}
		}
    	return null;
    }
    
    //@ requires 0 <= index && index < this.size();
    public Element get(int index) {
        Node p = getNode(index);
        return p.element;
    }

    //@ requires 0 <= i && i < this.size();
    private /*@ pure @*/ Node getNode(int i) {
        Node p = first;
        int pos = 0;
        while (pos != i) {
            p = p.next;
            pos = pos + 1;
        }
        return p;
    }

    //@ ensures \result >= 0;
    public /*@ pure @*/ int size() {
        return size;
    }

    public class Node {
        private Element element;
        public Node next;

        public Node(Element element) {
            this.element = element;
            this.next = null;
        }

        public Element getElement() {
            return element;
        }
    }
    

}
