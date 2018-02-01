bool scanReceived = FALSE, imageReceived = TRUE;
LaserScan scan; Image image;      
subscribe<LaserScan>("scan", scanCallback);
subscribe<Image>("/camera/rgb/image_color", imageCallback);            
   
while (ros::ok()) {   
    if (scanReceived && imageReceived) {             
      window.show(merge(scan, image)));
      scanReceived = FALSE;  imageReceived = FALSE;          
    }        
    ros::spinOnce();
}

void scanCallback(LaserScan newScan) {  
  if (!scanReceived) {        
    scan = newScan;    
    scanReceived = TRUE; 
  }
}

void imageCallback (Image newImage) {
  if (!imageReceived) {
    image = new Image(newImage);
    imageReceived = TRUE;
  }
}

Mat merge_stream(LaserScan scan, Image image) {
  Mat mat = OpenCV.convertToMat(image);
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
    return mat;  
}

