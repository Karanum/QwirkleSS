package ss.qwirkle;

import ss.qwirkle.common.Game;
import ss.qwirkle.common.Game.GameType;
import ss.qwirkle.common.player.AIPlayer;
import ss.qwirkle.common.player.HumanPlayer;
import ss.qwirkle.common.player.ai.BasicBehaviour;
import ss.qwirkle.common.ui.TUI;

/**
 * Main class for the client-side program.
 * @author Karanum
 */
public class QwirkleClient {

	public static void main(String[] args) {
		Game.type = GameType.SINGLEPLAYER;
		
		Game game = new Game();
		game.setup(new TUI(game));
		game.addPlayer(new HumanPlayer(game, "Mark"));
		game.addPlayer(new AIPlayer(game, "Dylan", new BasicBehaviour()));
		game.start();
	}
	
}
