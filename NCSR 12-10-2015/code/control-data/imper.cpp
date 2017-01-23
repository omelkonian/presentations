void handle_data(float val) {
	if (val > threshold)
		publish("cmd", act(val));
}
int main() {
	ROS.subscribe("sensor", handle_data);
	ROS.publish("cmd");
	...	
}