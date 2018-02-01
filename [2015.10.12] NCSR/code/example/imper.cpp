float arr[4] = {0, 0, 0, 0};
void callback_up(float val) { if (val > 0) arr[0] = val; }
void callback_down(float val) { if (val > 0) arr[1] = val; }
void callback_left(float val) { if (val > 0) arr[2] = val; }
void callback_right(float val) { 
	if (val > 0) arr[3] = val; 
	string cmd_ver = "", cmd_hor = "";
	
	if (arr[0] > arr[1]) cmd_ver = "UP"
	else if (arr[0] < arr[1]) cmd_ver = "DOWN"
	else cmd_vertical = ""	
	if (arr[2] > arr[3]) cmd_hor = "LEFT"
	else if (arr[2] < arr[3]) cmd_hor = "RIGHT"
	else cmd_hor = ""

	ROS.publish("cmd", cmd_ver + cmd_hor);
}
int main() {
	ROS.subscribe("sensor_up", callback_up); ROS.subscribe("sensor_down", callback_down);
	ROS.subscribe("sensor_left", callback_left); ROS.subscribe("sensor_right", callback_right);
	ROS.publisher("cmd");
	...	
}