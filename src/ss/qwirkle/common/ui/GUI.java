package ss.qwirkle.common.ui;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;
import java.util.List;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;

/**
 * A quick GUI test.
 * NOTE: Does not function the way it should! Please do not use!
 * 
 * @author Karanum
 */
public class GUI implements UI, ActionListener {

	JFrame window;
	JTextArea chatLog;
	JTextField textBar;
	JPanel leftPanel;
	JPanel rightPanel;
	
	String chat;
	
	public GUI() {
		chat = "";
		
		window = new JFrame("Qwirkle");
		window.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		
		leftPanel = new JPanel();
		leftPanel.setPreferredSize(new Dimension(480, 600));
		leftPanel.setMinimumSize(new Dimension(480, 600));
		leftPanel.setMaximumSize(new Dimension(480, 600));
		window.add(leftPanel, BorderLayout.LINE_START);
		
		rightPanel = new JPanel();
		rightPanel.setPreferredSize(new Dimension(320, 600));
		rightPanel.setMinimumSize(new Dimension(320, 600));
		rightPanel.setMaximumSize(new Dimension(320, 600));
		window.add(rightPanel, BorderLayout.LINE_END);
		
		constructGamePanel();
		constructChatPanel();
	}
	
	private void constructGamePanel() {
		JPanel gamePanel = new JPanel(new GridLayout(12, 16));
		gamePanel.setPreferredSize(new Dimension(480, 360));
		gamePanel.setMaximumSize(new Dimension(480, 360));
		leftPanel.add(gamePanel, BorderLayout.PAGE_START);
		
		for (int y = 0; y < 12; ++y) {
			for (int x = 0; x < 16; ++x) {
				JButton button = new JButton("*");
				button.setMinimumSize(new Dimension(30, 30));
				gamePanel.add(button);
			}
		}
	}
	
	private void constructChatPanel() {
		JPanel chatPanel = new JPanel(new BorderLayout());
		chatPanel.setPreferredSize(new Dimension(320, 420));
		rightPanel.add(chatPanel, BorderLayout.PAGE_END);
		
		chatLog = new JTextArea();
		chatLog.setEditable(false);
		chatPanel.add(chatLog, BorderLayout.CENTER);
		
		JScrollPane scrollBar = new JScrollPane(chatLog);
		scrollBar.setPreferredSize(new Dimension(320, 400));
		scrollBar.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED);
		scrollBar.setHorizontalScrollBarPolicy(JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);
		chatPanel.add(scrollBar, BorderLayout.EAST);
		
		textBar = new JTextField(30);
		textBar.addActionListener(this);
		chatPanel.add(textBar, BorderLayout.SOUTH);
		
		window.pack();
		window.setVisible(true);
	}
	
	@Override
	public void run() {
		// TODO Auto-generated method stub

	}

	@Override
	public void update() {
		// TODO Auto-generated method stub

	}

	@Override
	public void actionPerformed(ActionEvent e) {
		if (e.getSource() == textBar) {
			if (!chat.isEmpty()) {
				chat += "\n"; 
			}
			chat += textBar.getText();
			textBar.setText("");
			chatLog.setText(chat);
		}
	}

}
