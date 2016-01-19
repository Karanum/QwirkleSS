package ss.qwirkle.client.player.ai;

import java.util.List;
import java.util.Random;

import ss.qwirkle.client.Board;
import ss.qwirkle.client.Move;
import ss.qwirkle.client.tiles.Tile;

public class BasicBehaviour implements Behaviour {

	@Override
	public Move determineMove(Board b, List<Tile> hand) {
		Random r = new Random();
		Move move = new Move();
		boolean result = false;
		while (!result) {
			//if (b.canPlaceTile(tile, x, y))) {
			result = true;
				
			//}
		}
		return move;
	}
}