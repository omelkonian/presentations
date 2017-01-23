constant Kp, Ki, Kd, setpoint
Graph g = loop(output): 
	error = setpoint - output
	p = (*Kp) <<< error
	i = (*Ki) <<< integral <<< error
	d = (*Kd) <<< derivative <<< error
	result = sum [p, i, d]
	output <<< process <<< result
