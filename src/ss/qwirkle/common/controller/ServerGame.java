package ss.qwirkle.common.controller;

import java.util.List;

import ss.qwirkle.common.Move;
import ss.qwirkle.common.player.ClientPlayer;
import ss.qwirkle.common.player.Player;
import ss.qwirkle.common.tiles.Tile;
import ss.qwirkle.exceptions.InvalidMoveException;
import ss.qwirkle.exceptions.MoveOrderException;
import ss.qwirkle.network.ClientHandler;

public class ServerGame extends Game {

	public ServerGame(List<ClientHandler> handlers) {
		super();
		for (ClientHandler handler : handlers) {
			addPlayer(new ClientPlayer(this, handler, handler.getPlayerName()));
		}
	}
	
	@Override
	public void start() {
		// TODO Auto-generated method stub
	}

	@Override
	public GameEndCause testGameOver() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Player getLocalPlayer() {
		return null;
	}

	@Override
	public void tradeTiles(Player p, List<Tile> tiles) throws MoveOrderException {
		// TODO Auto-generated method stub
	}
	
	@Override
	//@ requires p != null && move != null;
	public void doMove(Player p, Move move) throws InvalidMoveException, MoveOrderException {
		if (p != getPlayers().get(currentPlayer)) {
			throw new MoveOrderException();
		}
		getBoard().doMove(move);
		p.addScore(move.getPoints());
		
		if (p instanceof ClientPlayer) {
			//((ClientPlayer) p).getHandler();
			//TODO: Send out move
		}
	}

}
