package week5;


import java.util.*;

public class MapUtil {
	/*@
	 @ ensures \result == (\forall K x1, K x2 : map.keySet()); x1 != x2; map.get(x1) != map.get(x2));
	 @ pure
	 */
    public static <K, V> boolean isOneOnOne(Map<K, V> map) {
        // TODO: implement, see exercise P-5.1
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
     * @ 
     * @ ensures \result == (\forall Object Y; range.contains(Y); \exist Object X; f.contains(X)); f.get(X).equals(Y); 
     */
    public static <K, V> 
    	boolean isSurjectiveOnRange(Map<K, V> f, Set<V> range) {
        // TODO: implement, see exercise P-5.2
    		for(V value : range){
    			if(!f.containsValue(value)){
    				return false;
    			}
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

    
    
    /*
     *@ensures \result == (\forall Object x; map.keySet().contains(x) ; \result.get(map.get(x)).equals(x);)
     */
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
    // @ requires MapUtil.isOneOnOne(map);
    // @ ensures \result.keyset.equals(map.values()) && \result.values().equals(map.keySet());
	// @ ensures (\forall Object x; map.values().contains(x); \result.get(map.get(x)).equals(x);
	public static <K, V> Map<V, K> inverseBijection(Map<K, V> map) {
        // TODO: implement, see exercise P-5.3
		Map <V, K> result = new HashMap<V, K>();
			for (K key : map.keySet()){
				result.put(map.get(key), key);
			}
		
        return result;
	}
	/*
	 * @ensures \result == (\forall Object x; f.keySet.contains(x); \result.get(x).equals(g.get(f.get(x)))
	 */
	public static <K, V, W> boolean compatible(Map<K, V> f, Map<V, W> g) {
        // TODO: implement, see exercise P-5.4
		
		for (V value : f.values()){
			if(!g.containsKey(value)){
				return false;
			}
		}
		
        return true;
	}
	
	
/*
 * @ requires compatible(f,g);
 * @ ensures (\forall Object x; f.keySet().contains(x); \result.keySet().contains(x) && \result.get(x).equals(g.get(f.get(x))));
 */
	
	public static <K, V, W> Map<K, W> compose(Map<K, V> f, Map<V, W> g) {
        // TODO: implement, see exercise P-5.5
		if (compatible(f, g)){
			Map<K,W> result = new HashMap <K,W>();
			for (K key : f.keySet()){
				
				result.put(key, g.get(f.get(key)));
				}
			
			return result;
		}
		return null;
	}
}
