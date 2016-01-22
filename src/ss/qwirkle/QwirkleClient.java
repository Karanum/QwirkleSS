package ss.qwirkle;

import ss.qwirkle.common.Game;
import ss.qwirkle.common.Game.GameType;
import ss.qwirkle.common.ui.GUI;

public class QwirkleClient {

	public static void main(String[] args) {
		Game.type = GameType.SINGLEPLAYER;
		
		Game game = new Game(new GUI());
		game.setup();
		game.start();
	}
	
}
