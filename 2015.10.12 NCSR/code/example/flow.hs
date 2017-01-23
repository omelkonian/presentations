Topic fused = zip 
		(subscribe "sensor_up",
		subscribe "sensor_down",
		subscribe "sensor_left",
		subscribe "sensor_right") 
		>>> filter (> 0)

Node actor = publish "cmd" (map act fused)

act (u,d,l,r) = ver ++ hor where 
	ver = if u>d "UP" else (if u<d "DOWN" else "")
	hor = if l>r "LEFT" else (if l<r "RIGHT" else "")