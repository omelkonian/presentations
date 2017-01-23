public Map<String, Topic> inputTopics() {
    Map<String, Topic> map = new HashMap<>();
    map.put("LASER", new Topic("/scan", LaserScan._TYPE));
    map.put("CAMERA", new Topic("/camera/rgb/image_color", Image._TYPE));
    map.put("DEPTH", new Topic("/camera/depth/image", Image._TYPE));
    map.put("TF", new Topic("/tf", TFMessage._TYPE));
    return map;
}

@Override
public Map<String, Topic> outputTopics() {
    return new HashMap<>();
}

@Override
public void dataflow() {
    // Visualization setup
    new Thread(() -> Application.launch(Visualizer.class)).start();
    Visualizer viz = Visualizer.waitForVisualizer();

    // Depth
    Stream.<Image>from(inputTopics().get("DEPTH")).flatMap(im -> {
        try {
            // Convert to grayscale
            im.setEncoding(ImageEncodings.RGBA8);
            Mat mat = CvImage.toCvCopy(im).image;
            Imgproc.cvtColor(mat, mat, Imgproc.COLOR_RGBA2GRAY);
            Imgproc.threshold(mat, mat, 150, 255, 0);
            return Stream.just(mat);
        } catch (Exception e) {
            return Stream.error(e);
        }
    }).sample(100, TimeUnit.MILLISECONDS)
      .subscribe(viz::displayDepth);        

    // TF        
    Stream.<TFMessage>from(inputTopics().get("TF"))
          .take(50)
          .collect((Func0<HashMap<String, Set<String>>>) HashMap::new, (m, msg) -> {
              List<TransformStamped> transforms = msg.getTransforms();
              for (TransformStamped transform : transforms) {
                  String parent = transform.getHeader().getFrameId();
                  String child = transform.getChildFrameId();
                  if (!m.containsKey(parent)) {
                      Set<String> init = new HashSet<>();
                      init.add(child);
                      m.put(parent, init);
                  }
                  else m.get(parent).add(child);
            }
          })
          .subscribe(viz::displayTF);

    // Laser
    Stream<LaserScan> laser = Stream.from(inputTopics().get("LASER"));
    // Colored image
    Stream<Mat> image = Stream.<Image>from(inputTopics().get("CAMERA")).flatMap(im -> {
        try {
            return Stream.just(CvImage.toCvCopy(im).image);
        } catch (Exception e) {
            return Stream.error(e);
        }
    }).sample(60, TimeUnit.MILLISECONDS) // backpressure
      .map(this::faceDetect); // Detect faces        
      
    // Embed laser
    Stream.combineLatest(laser, image, ControlPanel::embedLaser)
          .subscribe(viz::displayRGB);        

    // Battery
    Stream.interval(2, TimeUnit.SECONDS)
          .map(v -> (100 - v) / 100.0)
          .subscribe(viz::displayBattery);
}

private Mat faceDetect(Mat im) {
    if (Visualizer.faceDetection) {
        // Operate on gray-scale image
        Mat temp = new Mat();
        Imgproc.cvtColor(im, temp, Imgproc.COLOR_BGR2GRAY, 3);
        faceDetector.detectMultiScale(temp, faces, 1.15, 2, 0, new Size(im.rows() / 12, im.rows() / 12), new Size(im.rows() / 8, im.cols() / 8));
        for (Rect r : faces.toArray())
            Core.rectangle(im, new Point(r.x, r.y), new Point(r.x + r.width, r.y + r.height), new Scalar(0, 255, 0));
    }
    return im;
}

private static Mat embedLaser(LaserScan l, Mat im) {
    int width = im.cols(), height = im.rows();
    Point center = new Point(width / 2, height);
    float curAngle = l.getAngleMin();
    float[] ranges = l.getRanges();
    for (float range : ranges) {
        double x = center.x + (width / 2 * range * Math.cos(curAngle + Math.PI / 2));
        double y = center.y - (width / l.getRangeMax() * range * Math.sin(curAngle + Math.PI / 2));
        if (Math.abs(curAngle) < 0.3)
            Core.line(im, center, new Point(x, y), new Scalar(0, 0, 255));
        curAngle += l.getAngleIncrement();
    }
    Core.circle(im, center, 2, new Scalar(0, 0, 0), -1);
    return im;
}