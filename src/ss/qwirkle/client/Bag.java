package ss.qwirkle.client;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

import ss.qwirkle.client.tiles.Color;
import ss.qwirkle.client.tiles.Shape;
import ss.qwirkle.client.tiles.Tile;

/**
 * Container class for tiles that are not on the board or in a player's hand.
 * @author Karanum
 */
public class Bag {

	public static final int TILE_COPIES = 3;
	
	//@ private invariant bag != null;
	//@ private invariant rand != null;
	private List<Tile> bag;
	private Random rand;
	
	/**
	 * Creates a new bag and fills it with the initial list of tiles.
	 */
	public Bag() {
		bag = new ArrayList<Tile>();
		rand = new Random();
		for (Color color : Color.values()) {
			for (Shape shape : Shape.values()) {
				for (int i = 0; i < TILE_COPIES; ++i) {
					bag.add(new Tile(color, shape));
				}
			}
		}
		Collections.shuffle(bag, rand);
	}
	
	/**
	 * Returns a list of random tiles.
	 * @param amount Amount of tiles to return
	 */
	//@ requires amount > 0 && amount <= Player.MAX_HAND_SIZE;
	//@ ensures \result != null;
	//@ ensures \result.size() == amount;
	//@ ensures getSize() == (amount >= getSize() ? \old(getSize()) - amount : 0);
	public List<Tile> getTiles(int amount) {
		List<Tile> tiles = new ArrayList<Tile>();
		for (int i = 0; i < amount && getSize() > 0; ++i) {
			int randInt = rand.nextInt(getSize());
			Tile tile = bag.remove(randInt);
			tiles.add(tile);
		}
		return tiles;
	}
	
	/**
	 * Adds tiles back into the bag.
	 * @param tiles The list of tiles to add
	 */
	//@ requires tiles != null;
	//@ ensures getSize() == \old(getSize()) + tiles.size();
	public void returnTiles(List<Tile> tiles) {
		bag.addAll(tiles);
		Collections.shuffle(bag, rand);
	}
	
	/**
	 * Returns the amount of tiles left in the bag.
	 */
	//@ pure
	public int getSize() {
		return bag.size();
	}
	
}
