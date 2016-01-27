package ss.qwirkle.common.player;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import ss.qwirkle.common.Move;
import ss.qwirkle.common.controller.SingleplayerGame;
import ss.qwirkle.common.player.ai.Behaviour;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;
import ss.qwirkle.exceptions.MoveOrderException;

/**
 * A Player that makes use of a set Behaviour to determine its moves.
 * @author Karanum
 */
public class AIPlayer extends Player {

	//@ private invariant behaviour != null;
	private Behaviour behaviour;
	private SingleplayerGame game;
	
	private int tilesToTrade;
	private List<Tile> playedTiles;
	
	/**
	 * Creates a new AI player with the given name and behaviour.
	 * @param name The name of the new player
	 * @param ai The behaviour pattern of the player
	 */
	//@ requires name != null;
	//@ requires ai != null;
	//@ requires game != null;
	public AIPlayer(SingleplayerGame game, String name, Behaviour ai) {
		super(name);
		behaviour = ai;
		this.game = game;
		tilesToTrade = 6;
		playedTiles = new ArrayList<Tile>();
	}
	
	/**
	 * Asks the player to determine their next move using their behaviour.
	 */
	@Override
	public void determineMove() {
		tilesToTrade = 6;
		Move move = behaviour.determineMove(game.getBoard(), getHand());
		if (move.getTiles().size() > 0) {
			playedTiles = move.getTiles();
			try {
				game.doMove(this, move);
			} catch (InvalidMoveException e) {
				e.printStackTrace();
			} catch (MoveOrderException e) {
				e.printStackTrace();
			}
		} else {
			playedTiles = new ArrayList<Tile>(hand);
			hand.clear();
			try {
				game.tradeTiles(this, playedTiles);
			} catch (MoveOrderException e) {
				e.printStackTrace();
			}
		}
	}

	/**
	 * Used by the network client to notify that the player's trade failed.
	 */
	//@ requires message != null;
	@Override
	public void tradeFailed(String message) {
		hand.addAll(playedTiles);
		
		--tilesToTrade;
		playedTiles = new ArrayList<Tile>(hand);
		Collections.shuffle(playedTiles);
		while (playedTiles.size() > tilesToTrade) {
			playedTiles.remove(0);
		}
		
		hand.removeAll(playedTiles);
		try {
			game.tradeTiles(this, playedTiles);
		} catch (MoveOrderException e) {
			e.printStackTrace();
		}
	}
	
	/**
	 * Used by the network client to notify that the player's move failed.
	 */
	//@ requires message != null;
	@Override
	public void moveFailed(String message) {
		hand.addAll(playedTiles);
		determineMove();
	}
	
}
