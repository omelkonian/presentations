bool scanReceived = FALSE, imageReceived = TRUE;
LaserScan scan; Image image;
subscribe<LaserScan>("/scan", scanCallback);
subscribe<Image>("/camera/rgb", imageCallback);
// Main ROS loop
while (ros::ok()) {
    if (scanReceived && imageReceived) {
      window.show(embedLaser(scan, image));
      scanReceived = FALSE;  imageReceived = FALSE;
    }
    ros::spinOnce();
}
// Callback for topic "/scan"
void scanCallback(LaserScan newScan) {
  if (!scanReceived) {
    scan = newScan;
    scanReceived = TRUE;
  }
}
// Callback for topic "/camera/rgb"
void imageCallback (Image newImage) {
  if (!imageReceived) {
    image = new Image(newImage);
    imageReceived = TRUE;
  }
}
// OpenCV stuff...
Mat embedLaser(LaserScan scan, Image image) { ... }
