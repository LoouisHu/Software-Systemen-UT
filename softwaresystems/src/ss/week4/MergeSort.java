package ss.week4;

import java.util.LinkedList;

public class MergeSort {
	
	public static <E extends Comparable<E>> LinkedList<E> bubbleSort(LinkedList<E> output) {
		while (!validateList(output)) {
			LinkedList<E> array = new LinkedList<E>(output);
			output = new LinkedList<E>();
			
			E current = array.pollFirst();
			while (array.size() > 0) {
				E front = array.pollFirst();
				if (current.compareTo(front) > 0) {
					output.addLast(front);
				}
				else {
					output.addLast(current);
					current = front;
				}
			}
			
			E last = array.pollFirst();
			if (last == null) {
				output.addLast(current);
			}
			else {
				output.addLast(last);
			}
		}
		return output;
	}
	
	public static <E extends Comparable<E>> LinkedList<E> mergeSort(LinkedList<E> input) {
		LinkedList<LinkedList<E>> array = normalize(new LinkedList<E>(input));
		LinkedList<LinkedList<E>> output = new LinkedList<LinkedList<E>>(array);
		while (output.size() > 1) {
			output = new LinkedList<LinkedList<E>>();
			while (array.size() > 1) {
				output.addLast(merge(array.pollFirst(), array.pollFirst()));
			}
			if (array.size() > 0) output.addLast(array.pollFirst());
			array = output;
		}
		return output.pollFirst();
	}
	
	public static <E extends Comparable<E>> LinkedList<E> merge(LinkedList<E> l1, LinkedList<E> l2) {
		LinkedList<E> output = new LinkedList<E>();
		E cur1 = null;
		E cur2 = null;
		while (l1.size() > 0 || l2.size() > 0) {
			if (cur1 == null) {
				cur1 = l1.pollFirst();
			}
			if (cur2 == null) {
				cur2 = l2.pollFirst();
			}
			
			if (cur1 == null && cur2 != null) {
				output.add(cur2);
				cur2 = null;
			}
			if (cur2 == null && cur1 != null) {
				output.add(cur1);
				cur1 = null;
			}
			if (cur1 != null && cur2 != null) {
				if (cur1.compareTo(cur2) <= 0) {
					output.add(cur1);
					cur1 = null;
				} else {
					output.add(cur2);
					cur2 = null;
				}
			}
		}
		if (cur1 == null && cur2 != null) {
			output.add(cur2);
			cur2 = null;
		}
		if (cur2 == null && cur1 != null) {
			output.add(cur1);
			cur1 = null;
		}
		return output;
	}
	
	public static <E extends Comparable<E>> LinkedList<LinkedList<E>> normalize(LinkedList<E> input) {
		LinkedList<E> array = new LinkedList<E>(input);
		LinkedList<LinkedList<E>> output = new LinkedList<LinkedList<E>>();
		while (array.size() > 0) {
			LinkedList<E> tmplist = new LinkedList<E>();
			tmplist.add(array.pollFirst());
			output.add(tmplist);
		}
		return output;
	}
	
	public static <E extends Comparable<E>> boolean validateList(LinkedList<E> input) {
		LinkedList<E> array = new LinkedList<E>(input);
		
		E current = array.pollFirst();
		while (array.size() > 0) {
			E next = array.pollFirst();
			if (current.compareTo(next) > 0) {
				return false;
			}
			current = next;
		}
		return true;
	}
	
	public static void main(String[] args) {
		LinkedList<Integer> list = new LinkedList<Integer>();
		list.add(5);
		list.add(3);
		list.add(4);
		list.add(2);
		list.add(1);
		list.add(6);
		list.add(10);
		System.out.println(bubbleSort(list));
		System.out.println(mergeSort(list));
	}
}