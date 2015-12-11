package week5;

import static org.junit.Assert.assertTrue;

import java.util.*;

public class MapUtil {
    public static <K, V> boolean isOneOnOne(Map<K, V> map) {
        // TODO: implement, see exercise P-5.1
    	/* @ requires map != null;
    	 * @ ensures x1 != x2;
    	 * @ ensures \result == \forall (x1, x2 : map.entrySet());
    	 * @ ensures x1.getValue() == x2.getValue()
    	 * @ pure
    	 */

    	for(Map.Entry<K, V> x1 : map.entrySet() ){
    		for(Map.Entry<K, V> x2 : map.entrySet()){
    			if (x1 != x2){
    				if (x1.getValue() == x2.getValue())  {  					
//    				if (map.get(x1.getKey()).equals(map.get(x2.getKey()))){
    					return false;
    				}
    			}
    		}
    	}
    	return true;
    	
    	}
    /* @ pure;
     * @ ensures f != null;
     * @ ensures \result == (\forall range;
     * @ ensures 
     */
    public static <K, V> 
    	boolean isSurjectiveOnRange(Map<K, V> f, Set<V> range) {
        // TODO: implement, see exercise P-5.2
   
    		if(!f.containsValue(range)){
    			return false;
    		}
    	
    	return true;
    }
//    	for (V y : range){
//    		boolean foundKey = false;
//    		for(K x : f.keySet()){
//    			if (f.get(x) == y){
//    				foundKey = true;
//    				break;
//    			}
//    		}
//    		if (!foundKey){
//    			return false;
//    		}
//    	}
//    	return true;
    // @requires map != null;
    // @ensures (\forall V y ; \result.containsKey(y))
    public static <K, V> Map<V, Set<K>> inverse(Map<K, V> map) {
        // TODO: implement, see exercise P-5.3
    	Map<V, Set<K>> result = new HashMap<V, Set<K>>();
    	for (V y : map.values()){
    		Set<K> alleXen = new HashSet<K>();
    		for (K x : map.keySet()){
    			if (map.get(x) == y){
    				alleXen.add(x);
    			}
    		}
    		result.put(y, alleXen);
    	}
    	return result;
    }
    //@ensures map != null;
    //@ensures 
	public static <K, V> Map<V, K> inverseBijection(Map<K, V> map) {
        // TODO: implement, see exercise P-5.3
		Map <V, K> result = new HashMap<V, K>();
		for (V value : map.values()){
			for (K key : map.keySet()){
				if (map.get(key) == value) {
					result.put(value, key);
					break;
				}
			}
		}
        return result;
	}
	
	public static <K, V, W> boolean compatible(Map<K, V> f, Map<V, W> g) {
        // TODO: implement, see exercise P-5.4
		
		for (V value : f.values()){
			if(!g.containsKey(value)){
				return false;
			}
		}
		
        return true;
	}
	public static <K, V, W> Map<K, W> compose(Map<K, V> f, Map<V, W> g) {
        // TODO: implement, see exercise P-5.5
		Map<K,W> result = new HashMap <K,W>();
		
		//for (K key)
        return null;
	}
	public static void main(String[] args){
		Map lmao = new HashMap();
		lmao.put(1, 3);
		lmao.put(2, 3);
		lmao.put(2, 3);
		System.out.println(isOneOnOne(lmao));
	}
}
