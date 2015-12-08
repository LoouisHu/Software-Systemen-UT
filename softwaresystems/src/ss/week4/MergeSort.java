package ss.week4;

import java.util.*;

public class MergeSort {
	public static <E extends Comparable<E>>
	
	List<E> mergesort(List<E> list){
		List<E> res = new ArrayList();
		if (list.size() <= 1){
			res = list;
		} else {
			int i = list.size() / 2;
			List<E> fst = mergesort(list.subList(0, i));
			List<E> snd = mergesort(list.subList(i, list.size() ));
			int fi = 0;
			int si = 0;
			while (fi < fst.size() && si < snd.size()) {
				if (fst.get(fi).compareTo(snd.get(si) < 0) ){
					res.add(fst.get(fi));
					fi = fi + 1;
				} else {
					res.add(snd.get(si));
					si = si + 1;
				}
			}
			if (fi < fst.size()) {
				res.addAll(fst.subList(fi, fst.size()));
			}
			if (si < snd.size()) {
				res.addAll(snd.subList(si, snd.size()));
			}
		}
		return res;
	}
}