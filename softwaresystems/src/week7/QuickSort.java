package week7;

import java.util.HashMap;

public class QuickSort extends Thread {
	public static HashMap<int[], String[]> threadList = new HashMap<int[], String[]>();

	private int[] a;
	private int first, last;

	public static void qsort(int[] a) {
		Thread t = (new QuickSort(a, 0, a.length - 1));
		t.start();
		try {
			t.join();
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public static void qsort(int[] a, int first, int last) {
		if (first < last) {
			int position = partition(a, first, last);
			Thread t1, t2;
			t1 = (new QuickSort(a, first, position - 1));
			t2 = (new QuickSort(a, position + 1, last));
			t1.start();
			t2.start();
			try {
				t1.join();
				t2.join();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}

	public static int partition(int[] a, int first, int last) {

		int mid = (first + last) / 2;
		int pivot = a[mid];
		swap(a, mid, last); // put pivot at the end of the array
		int pi = first;
		int i = first;
		while (i != last) {
			if (a[i] < pivot) {
				swap(a, pi, i);
				pi++;
			}
			i++;
		}
		swap(a, pi, last); // put pivot in its place "in the middle"
		return pi;
	}

	public static void swap(int[] a, int i, int j) {
		int tmp = a[i];
		a[i] = a[j];
		a[j] = tmp;
	}

	public QuickSort(int[] a, int first, int last) {
		this.a = a;
		this.first = first;
		this.last = last;
	}

	public void run() {
		qsort(a, first, last);
	}

    
}
