package ss.qwirkle.network;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;

public class Client extends Thread {
	
	private String clientName;
	private Socket sock;
	private BufferedReader in;
	private BufferedWriter out;
	
	public Client(String name, InetAddress host, int port) throws IOException {
		clientName = name; 
		try {
			sock = new Socket(host, port);
	    	in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
	    	out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
        } catch (IOException e) {
            System.out.println("ERROR: could not create a socket on " + host
                    + " and port " + port);
		}	
	}
	public String getClientName() {
		return clientName;
	}
	/** send a message to a ClientHandler. */
	public void sendMessage(String message) {
		try {
			out.write(message);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			System.out.println("Connection has been lost.");
			shutdown();
		}
    }
	/** close the socket connection. */
	public void shutdown() {
		print("Closing socket connection...");
		try {
			sock.close();
			in.close();
			out.close();
			System.exit(0);
		} catch (IOException e) {
			e.printStackTrace();
		}	
	}
	private static void print(String message) {
		System.out.println(message);
	}
}
