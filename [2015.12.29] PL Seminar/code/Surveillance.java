Topic CAMERA = new Topic("/camera/rgb/image_color", Image._TYPE);

Stream<Mat> image = Stream.<Image>from(CAMERA).map(OpenCV::convertToMat);    
Stream<Mat> initial = image.take(1).repeat();
Stream.zip(image, initial, Pair::new)
      // stop monitoring when video stream stops
      .timeout(1, TimeUnit.MINUTES)
      .doOnCompleted(this::shutdown) 
      // Only stream images when motion is detected
      .filter(Surveillance::motionDetected) 
      .map(Pair::getLeft)
      .subscribe(window::showImage);
