// RHEA setup
Stream.configure(new HazelcastDistributionStrategy(
   	RxjavaEvaluationStrategy::new,
   	RosEvaluationStrategy::new,
   	MqttEvaluationStrategy::new));
// Topics
Topic<RobotCommand> vel = new RosTopic<>("/robot/cmd");
Topic<Proximity> ble = new MqttTopic<>("/ble");
// Running on smartphone
Stream.from(ReactiveBeacons.observe())
      .map(Beacon::getProximity)
      .subscribe(ble);
// Running on robot
Stream<Proximity> prox = Stream.from(ble);
prox.filter(Proximity::isNear)
    .map(d -> Commands.SPEED_UP)
    .subscribe(vel);
prox.filter(Proximity::isFar)
    .map(d -> Commands.SLOW_DOWN)
    .subscribe(vel);
