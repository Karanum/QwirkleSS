package ss.qwirkle.network;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;

public class ClientHandler extends Thread {
	
    private Server server;
    private BufferedReader in;
    private BufferedWriter out;
    private String clientName;
	
	public ClientHandler(Server server, Socket sock) throws IOException {
		this.server = server;
    	in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
    	out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
		
	}
    private void shutdown() {
        server.removeHandler(this);
        server.broadcast("[" + clientName + " has left]");
    }
    public void announce() throws IOException {
        clientName = in.readLine();
        server.broadcast("[" + clientName + " has entered]");
    }
    public void sendMessage(String message) {
        try {
        	out.write(message);
        	out.newLine();
        	out.flush();
        } catch (IOException e) {
        	shutdown();
        }
    }
    public void run() {
    	while (true) {
    		try {
    			String line = in.readLine();
    			if (line != null) {
    				server.broadcast(clientName + ": " + line);
    			}
    		} catch (IOException e) {
    			shutdown();
    		}
    	}
    }
}
