// Sensors
Topic LASER = new Topic("/scan", LaserScan._TYPE);
Topic CAMERA = new Topic("/camera/rgb/image_color", Image._TYPE);
Topic DEPTH = new Topic("/camera/depth/image", Image._TYPE);
Topic TF = new Topic("/tf", TFMessage._TYPE);
// Actuators
Topic CMD = new Topic("/cmd_vel", VelCmd._TYPE);

Stream.setEvaluationStrategy(new RxjavaEvaluationStrategy());

// ROS topics
Stream<Point> laser = Stream.from(LASER).filter(LaserScan::valid).map(LaserScan::getCartesianPoint);
Stream<Mat> image = Stream.<Image>from(CAMERA).map(OpenCV::convertToMat);
Stream<TFMessage> tf = Stream.from(TF);
Stream.<Image>from(DEPTH).map(OpenCV::convertToGrayscale).subscribe(viz::displayDepth);

// Embed laser in color image
Stream.combineLatest(laser, image, (l, im) -> return im.embed(l))
    // Detect faces
    .sample(100, TimeUnit.MILLISECONDS)
    .map(this::faceDetect)
    // Display
    .subscribe(viz::displayRGB); 





// TF frames
tf.take(50).collect(HashMap::new, (map, msg) -> {
    List<TransformStamped> transforms = msg.getTransforms();
    for (TransformStamped transform : transforms) {
        String parent = transform.getHeader().getFrameId();
        String child = transform.getChildFrameId();
        if (!map.containsKey(parent)) {
            Set<String> init = new HashSet<>();
            init.add(child);
            map.put(parent, init);
        } else map.get(parent).add(child);
    }
})
.subscribe(viz::displayTF);

// Battery
Stream.interval(2, TimeUnit.SECONDS).map(v -> (100 - v) / 100.0).subscribe(viz::displayBattery);

// Control
Stream.<KeyEvent>from(KEYBOARD).map(CmdVel::new).subscribe(CMD);