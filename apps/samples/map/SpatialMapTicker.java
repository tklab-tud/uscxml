/**
 * Compile as:
 * $ javac -cp .:/usr/local/share/umundo/java/umundo.jar SpatialMapTicker.java
 *
 * Run as:
 * $ java -cp .:/usr/local/share/umundo/java/umundo.jar SpatialMapTicker
 */
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.LinkedList;
import java.util.Random;

import org.umundo.core.Greeter;
import org.umundo.core.Message;
import org.umundo.core.Node;
import org.umundo.core.Publisher;

public class SpatialMapTicker {

	Node node;
	Publisher pub;
	Greeter greeter;
	ArrayList<Sensor> sensors = new ArrayList<Sensor>(); 
	static ArrayList<SensorMessage> messages = new ArrayList<SensorMessage>();
	static Random random = new Random(System.currentTimeMillis());

	public class SensorMessage {
		public String message;
		public int severity;
		public SensorMessage(String message, int severity) {
			this.message = message;
			this.severity = severity;
		}
		public SensorMessage(String message) {
			this.message = message;
			this.severity = 3;
		}
	}
	
	public class Sensor {
		@Override
		public String toString() {
			return "Sensor [id=" + id + ", lat=" + lat + ", lon=" + lon
					+ ", html=" + getHTML() + "]";
		}
		public String id = "";
		public Double lat = new Double(0);
		public Double lon = new Double(0);
		LinkedList<SensorMessage> messages = new LinkedList<SensorMessage>(); 

		public void addMessage(SensorMessage message) {
			if (messages.size() > 15)
				messages.removeLast();
			messages.addFirst(message);
		}
		
		public String getHTML() {
			StringBuilder sb = new StringBuilder();
			for (SensorMessage message : messages) {
				sb.append(message.severity);
				sb.append(": ");
				sb.append(message.message);
				sb.append("<br />");
			}
			return sb.toString();
		}
	}
	
	public class SensorGreeter extends Greeter {
		public void welcome(Publisher publisher, String nodeId, String subId) {
			// send all sensors to new subscribers
			for (Sensor sensor : sensors) {
				Message msg = new Message(); //Message.toSubscriber(subId);
				msg.putMeta("id", sensor.id);
				msg.putMeta("lat", sensor.lat.toString());
				msg.putMeta("lon", sensor.lon.toString());
				msg.putMeta("html", sensor.getHTML());
				pub.send(msg);
			}
		}

		@Override
		public void farewell(Publisher arg0, String nodeId, String subId) {
		}
		
	}
	
	public SpatialMapTicker() {
		node = new Node();
		pub = new Publisher("map/tick");
		greeter = new SensorGreeter();
		pub.setGreeter(greeter);
		node.addPublisher(pub);
		
		double latCenter = 59.32;
		double lonCenter = 18.08;
		
		int nrSensors = 15; //(int) (Math.random() * 20);
		for (int i = 0; i < nrSensors; i++) {
			Sensor sensor = new Sensor();
			double latOffset = (Math.random() - 0.5) * 0.3;
			double lonOffset = (Math.random() - 0.5) * 0.3;

			sensor.id = "Sensor #" + i;
			sensor.lat = latCenter + latOffset;
			sensor.lon = lonCenter + lonOffset;
			sensors.add(sensor);
		}
	}

	public static void main(String[] args) {
		SpatialMapTicker ticker = new SpatialMapTicker();
		ticker.run();
	}

	private void run() {
		messages.add(new SensorMessage("Oil pressure threshold exceeded"));
		messages.add(new SensorMessage("Equipment is on fire"));
		messages.add(new SensorMessage("Error #32 in diagnostics unit"));
		messages.add(new SensorMessage("Unauthorized startup"));
		messages.add(new SensorMessage("Tire pressure too low"));
		messages.add(new SensorMessage("Error #145 in diagnostics unit"));
		messages.add(new SensorMessage("Unit was moved out of construction site area"));
		messages.add(new SensorMessage("Hydraulic pressure exceeding safety limits"));
		messages.add(new SensorMessage("Drivers seat belts are not fastened!"));
		messages.add(new SensorMessage("Battery recharge cycles exceeded"));
		messages.add(new SensorMessage("Unit operated outside recommended paramters"));

		while (true) {
			try {
				Thread.sleep((long) (Math.random() * 300) + 100);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
			
			Sensor sensor = sensors.get(random.nextInt(sensors.size()));
			SensorMessage fault = messages.get(random.nextInt(messages.size()));

			Date now = new Date();
			SimpleDateFormat sdf = new SimpleDateFormat("HH:mm:ss z");
			String nowString = sdf.format(now);
			sensor.addMessage(fault);
			
//			System.out.println("Publishing " + sensor);
			
			Message msg = new Message();
			msg.putMeta("id", sensor.id);
			msg.putMeta("lat", sensor.lat.toString());
			msg.putMeta("lon", sensor.lon.toString());
			msg.putMeta("html", sensor.getHTML());
			msg.putMeta("time", nowString);
			msg.putMeta("timeStamp", Long.toString(now.getTime()));
			msg.putMeta("message", sensor.messages.getFirst().message);
			msg.putMeta("severity", Integer.toString(random.nextInt(10)));
			pub.send(msg);
		}
	}

}
