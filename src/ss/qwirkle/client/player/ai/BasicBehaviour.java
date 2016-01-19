package ss.qwirkle.client.player.ai;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

import ss.qwirkle.client.Board;
import ss.qwirkle.client.Move;
import ss.qwirkle.client.tiles.Tile;

public class BasicBehaviour implements Behaviour {

	@Override
	public Move determineMove(Board b, List<Tile> hand) {
		//for loop with possibleLocations
		//for loop with possibleMoves
		//check if move can be done at tile.
		//if can be done return move and result = true;
		//else remove tile from possibleMoves
		List<Tile> myTiles = new ArrayList<Tile>(hand);
		Random r = new Random();
		Move move = new Move();
		Collections.shuffle(myTiles, r);
		List<Tile> possibleTiles = 
		Collections.shuffle(possibleTiles r);
		boolean result = false;
		while (!result) {
			for (Tile boardTile : possibleTiles) {
				int x = boardTile.getX();
				int y = boardTile.getY();
				for (Tile tile : myTiles) {
					if (!result && !b.hasTile(x + 1, y)) {
						for (Tile tile : myTiles) {
							//positie waar geen tile ligt.
							if (b.canPlaceTile(tile, x, y)) {
								result = true;
					}
					if (!result && !b.hasTile(x - 1, y)) {
						for (Tile tile : myTiles) {
							//positie waar geen tile ligt.
							if (b.canPlaceTile(tile, x, y)) {
								result = true;
					}
					if (!result && b.hasTile(x, y + 1)) {
						for (Tile tile : myTiles) {
							//positie waar geen tile ligt.
							if (b.canPlaceTile(tile, x, y)) {
								result = true;
					}
					if (!result && !b.hasTile(x, y + 1)) {
						for (Tile tile : myTiles) {
							//positie waar geen tile ligt.
							if (b.canPlaceTile(tile, x, y)) {
								result = true;
								
					} else { myTiles.remove(tile);
				}
			}	
		}
		return move;
	}
}