package ss.week4;

import java.util.*;

public class MergeSort {
	public static <E extends Comparable<E>>
	List<E> mergesort(List<E> list){
		List <E> = new ArrayList();
		if (list.size() > 1){
			int i = list.size() / 2;
			List<E> fst;
			List<E> snd;
			if (i >= 2){
				fst = list.subList(list.subList(0, i));
				snd = list.subList(list.subList(i, list.size()-1));
				fst = mergesort(fst);
				snd = mergesort(snd);
				
			}
			
		}
	}
}