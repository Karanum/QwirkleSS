package ss.qwirkle;

import ss.qwirkle.common.Game;
import ss.qwirkle.common.Game.GameType;
import ss.qwirkle.common.ui.GUI;
import ss.qwirkle.common.ui.TUI;

public class QwirkleClient {

	public static void main(String[] args) {
		Game.type = GameType.SINGLEPLAYER;
		
		Game game = new Game();
		game.setup(new TUI(game));
		game.start();
	}
	
}
