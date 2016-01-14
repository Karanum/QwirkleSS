package ss.qwirkle.client;

public interface Pattern {
	
	public boolean canMerge(Pattern pattern);
	
	public boolean canAdd (Tile tile);
		
	public void merge (Pattern pattern);
	
	public void add(Tile tile);
	
	public void getPoints();

}
