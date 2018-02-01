Topic LASER = new Topic("/scan", LaserScan._TYPE);
Topic CAMERA = new Topic("/camera/rgb/image_color", Image._TYPE);

Stream.setEvaluationStrategy(new RosEvaluationStrategy());

// ROS Topics
Stream<LaserScan> laser = Stream.from(LASER).filter(LaserScan::valid);
Stream<Mat> camera = Stream.from(CAMERA).map(OpenCv::convertToMat);

// Combine
Stream.combineLatest(laser, camera, (l, im) -> {    
    int width = mat.width(), height = mat.height();
    Point center = new Point(width / 2, height);
    float curAngle = l.getAngleMin();
    for (float r : l.getRanges()) {
        double x = (center.x + (width / 2 * r * Math.cos(curAngle + Math.PI / 2)));
        double y = (center.y - (width / l.getRangeMax() * r * Math.sin(curAngle + Math.PI / 2)));
        if (Math.abs(curAngle) < 0.3)
            Core.line(mat, center, new Point(x, y), new Scalar(0, 0, 255));
        curAngle += l.getAngleIncrement();
    }
    Core.circle(mat, center, 2, new Scalar(0, 0, 0), -1);
    return im;
}).subscribe(window::show);

