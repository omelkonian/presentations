INTRO
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Hello everyone, I am Orestis and this is joint work with Angelos Charalambidis, and is a result of an internship I did in a robotics research lab in Greece and also the topic of my bachelor thesis.

I am also glad to say that we published this paper and I will present it next week in the REBLS workshop at SPLASH in Boston.

And the title is:
"RHEA: ... "
oh, that's a mouthful... But let's first see how the

ANCIENT GREECE
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

if you go for a walk in Utrecht and enter the Centraal Museum, you can find this painting by an early 17th century Utrecht painter called Johanes Moreelse,
which depicts the ancient greek philosopher Heraclitus.

His most famous quote is "Panta rei" which means (everything flows)" and comes
from the verb ρεω (to flow/stream). This quote nicely summarizes his philosophy, which emphasized the contantly-changing nature of the
world, that everything moves and nothing remains still, and so forth...

In fact, the name of our framework is etymologically derived from the same verb, and it is the name of the daughter of Uranus and Gaia and mother of all Olympian gods!!

So, I have explained how the acronym came to be, and the rest of the talk will
try to convince you that the adjectives that it expanded to are actually justified.

DATAFLOW
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Now a computational model that embodies this philosophy quite faithfully, is the dataflow model.

In contrast to the traditional von-Neumann model, we have a fully-decentralized
set of individual computational nodes that communicate data with each other via the dataflow edges.

We have a complete absense of control-flow structures (like `if` statements)
and no shared state, which makes execution implicitly concurrent!

As an example, we see a simple dataflow graph that calculates the set of natural numbers.

We start with the singular value 0, and then proceed to a feedback loop which increments the numbers by 1.
So, in the output edge we have the sequence of natural numbers.

Now, to see in what way this execution can be parallelized, let's assume on the far right you have an output node that prints its arguments. Tracing the initial value 0, we see that after it leaves the `concat` node it will be processed concurrently by the output node and the increment node.

MOTIVATION
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

There are quite a few application domains which naturally fit the dataflow model.

- `Sensor-based systems`, such as robotics and IoT, are very naturally expressed as dataflow graphs, since you always have sensors that provide continuous streams of information that you process and transform in whatever way, eventually leading to an actuator that will perform actions on the output stream.

- Another application domain is `Big Data`, where you have enormous amount of continuous streams of information (think of tweets or click-streams) and you need to process them in a scalable and efficient manner. There are many dataflow frameworks, such as
  + Apache´s flink
  + Google´s map-reduce which is a degenerate form of a dataflow graph
  + and Microsoft's ReactiveExtensions which was actually developed by our very own Erik Meijer (I think he did a post-doc here, right?).

- We also see a lot of dataflow incluences in `interactive systems`, where you have to respond to user input such as UIs and games.
In the functional programming world, game libraries like Yampa embrace the FRP paradigm, which is very closely related with the dataflow model.

- And an example I should mention due to its high popularity,
is `TensorFlow`, a neural network construction library, where the user immediately writes dataflow graphs (representing neural-nets) and the backend then optimizes them, distibutes them over many devices, CUDA cores, and so forth...

MOTIVATION: ROBOTICS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Diving a bit deeper in Robotics now, the so called `RPA` where the robot senses information from its environment processses it and then acts on it to change its environment, is basically a dataflow graph.

Moreover, if you look into a `Control Theory` book, you will see a lot of dataflow diagrams inside, such as the famous PID feedback loop controller, which tries to reach a desired value by iteratively calculating an error and trying to minimize that.

ROS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
On the programming side of things, robotic applications are most oftenly written in the `ROS` (ROS for short), which is a middleware that provides a PubSub kind-of messaging platform for different robots to communicate via messages on named topics. And this again can be viewed as a dataflow graph where the input streams are the topics that clients publish to and the output nodes are the topics that clients listen to.

Now, the problem here is how they program these things!
Here we see an example where we have 2 sensors (1 for the laser scan and 1 for the camera feed of the robot) and you combine them to show images with the laser information embedded in it by drawing them as red lines.

So what you do is subscribe to certain topics and register a callback function for each one, that will be called whenever a message arrives there.
And you have this ugly main loop that you check things, your callbacks use global variables and it's all spaghetti and for larger examples you cannot handle the callback hell that arises (think of early JS days).

RHEA
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
And that's exactly what our framework is trying to overcome, by having the user write in a declarative stream language. This will internally be a dataflow graph that we can then optimize, distribute across multiple machines, and evaluate using one or more EvaluationStrategies.

To make our framework abstract and extensible, all the components here (except the stream language itself) use the so-called Strategy design pattern, where the base library provided the interfaces, and other libraries can provide their own backends.

Our framework is built for the JVM, we mainly support Java or Scala for the Stream language, but of course you can use whatever JVM language you like. And the whole ecosystem resides in a Github organisation called `rhea-flow`, where you have `rhea-core` that provides the stream language, all the pluggable interfaces and some sane defaults, and you other libraries that provide their own strategies. For instance, `rx-eval` evaluates a dataflow graph by translating it to RxJava operations and `ros-eval` knows how to handle ROS topics as source/sink nodes, and so on and so forth.

Up to now, we can say that by the design itself our framework is abstract since it is, in principle, not constained by technical details and allows for maximum flexibility in the implementations.

STREAM LANGUAGE
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Let us see how the Stream language look like.

You have source nodes that provide the initial values, which can also come from a Topic as we said before, and then you have single-input nodes, like `map` here, that transform a single stream of values.

We can also have multiple-input nodes that combine multiple stream, such as `zip` that provides a value from combining an element of each of the incoming streams.

You can also bind a stream to a variable and re-use to allow sharing, and in the graph view you would have split that takes the same stream to two processing nodes.

And lastly, you can have cycles by using the syntax of the loop operator, which I hope it's intuitive. The inner lambda take the so-far constructed graph and continues the pipeline, but its output will be fed back to the merging point, which is always a concat node. So our previous natural numbers example is easily translated to the code on the left.

Now, since our execution is completely demand-driven, these graphs would just sit there and never be evaluated. So the last ingredient is placing a final output node (using the `subscribe` method) that actually acts on the resulting stream and triggers the whole evaluation.

With these kind of nodes, you can build any graph you might want to, and we have many operators that you can use and there is a very nice diagrammatical way to document them, the so-called Marble Diagrams.

You have input streams on the top and the resulting stream on the bottom, and then use colors and numbers to make you point.

An important thing I haven't mentioned is that streams can be finite, but either sending a `COMPLETE` signal or an `ERROR` signal. So here we see that merge just combines the input streams in arbitrary order and completes if either of its input streams completes.

And you have many operators, like `filter`,`takeWhile`,`scan` (which is a fold that emits all its intermediate results), `sampling` to allow for backpressure which means you want to manage the load of your processing pipeline.

OPTIMIZATIONS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Before evaluating a given dataflow graph, our current default optimization strategy, will apply two stages of semantics-preserving transformations, namely ProactiveFiltering and GranularityAdjustment.

`Proactive filtering`, as the name suggests, tries to move filtering operations as early as possible in the pipeline. And although it might cost us a bit of computation time, it will certainly reduce the amount of data being transfered through dataflow edges, which can actually connect two different devices of the network, hence incurring significant communication overhead.
Just a few demonstrative examples here, a take after a map can always come before without changing the semantics, a filter after a map can be replaced with a filter of the composition and then the map, and we can move a filter after a concat to all of its input streams.

Now, the `NetworkProfilingStrategy` will detect how many resources are available (for instance, CPU cores) and will instruct the `OptimizationStrategy` to try reach this desired granularity. And it does so, by merging nodes when possible, such as replacing two maps with a single map of the composition or inlining maps on the inputs streams of a zip inside the zip node.

APPLICATION: ROBOT PANEL
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Let's see an actual example to make everything clear.

The goal is to monitor a robot by displaying useful information about it in a GUI on your computer, by utilizing the sensor information of 3 ROS topics.
- The `camera` topic that provides the image feed from the robot's camera.
- The `laser` topic that provides depth information.
- And the `tf` topic, which is a bit more complicated. The robot operates on different coordinate systems that form a hierarchy (think of it as scenes contained within other scenes that form some kind of tree). Now the robot emits messages that witness a single parent-child relation in that tree. So it will say this node is the parent of some other node, and after some time, this same node is the parent of another node, etc..

And because we do not have battery information from the sensors, we just mock one by using `interval` that provides the natural numbers in a timely manner.

So let's see the actual code!
I have kept the Visualization in a separate class, for you not to see the gory details of the UI code, that sets up the GUI window, etc...

We start by defining the three topics that we'll use, by setting the topic's name and type of values it carries.

Then we set the RosEvaluationStrategy that knows how to handle ROS topics, and internally uses RxJava to compute the maps, the folds and what have you.

And then we can get the streams out of these topics, where in the camera we need to do a conversion to an image format we can work, apply some backpressure, and run face detection using a trained classifier that will draw boxes around the faces it detects.

What we do now is combine the image and laser streams using the `embedLaser` function that will draw the laser as red lines in the image (let's not go into the details of the OpenCV code that does this). And instead of using `zip` here, we use `combineLatest` that immediately when a new element comes from either stream, will zip it with latest from the other stream. So it is like a more responsive version of `zip`.
And, of course, we subscribe the action to visualize the result.

Then, for the `tf` hierarchy we use collect, which is basically a fold that threads a data structure (in our case a `HashMap`). And after a finite number of observed relations will display it on the GUI.

And finally, the mocked battery that does this naive steady decrease of the battery level.

Let's see it running now!
We have to setup a ROS master server, which acts as the broker in the PubSub system and the `RosEvaluationStrategy` knows how to connect to it.
And because we don't have an actual robot here, we will play recorded data that are kept in the so-called `rosbag` files.

We can see on the right that the hierarchy is displayed properly, the mocked battery is slowly decreasing, we can enable face detection, and the laser lines become smaller as we approach the person.

So, from this example I think we can see that our system is reactive.

APPLICATION: ROBOT HOSPITAL GUIDE
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Let us now see a more heterogeneous example, where we use both a robot and an IoT device. In Iot you have a very similar PubSub middleware like ROS, called MQTT.

Our goal is to have a robot guided patients in different parts of a hospital (such as the cafeteria) and
assuming the robot knows how to do path planning, obstacle avoidance, etc.. we need to be able to adjust its speed according to the position of the patient.
We do so, by having the patient carry a smartphone that emits BLE signals (BLE for short), and the robot having a BLE receiver.

The dataflow graph is rather simple, we have an MQTT topic "ble",
we split this stream of signals, and map the ones that are near to SPEED_UP commands and the ones that are far away to SLOW_DOWN commands, and finally subscribe to the ROS topic, that controls the velocity of the robot's motors.

Now the setup code for this is a bit more involved than the previous example, because we need to have a distribution strategy that will run different parts of the dataflow to different devices, and we now also
need the MqttEvalStrategy to handle the MQTT topic.

We define our two topics, one for ROS and one for MQTT and then define 2 dataflows:
- the first one runs on the patient's smartphone and published its bluetooth signal to the "ble" topic
- and the second one runs on the robot and transforms the proximity information that it listens on the "ble" topic to the actuator commands for the robot's motors.


And in this example, we see how nicely RHEA can be used high-level declarative coordination language that glues together different parts of the system, running on different devices, and so forth...

So the motto here is: "dataflow in the large, and whatever in the small according to your needs"

DISTRIBUTION
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Let's see in a bit more detail how distribution works.

First of all, the granularity adjustment optimization that we saw may not be able to reach the desired number of nodes, so it the DistributionStrategy will now fuse parts of the dataflow graph into singular tasks, that can be run concurrently.

The most important step is to cleverly place this tasks on the network,
making sure that the communication overhead is as small as possible,
while satisfying some hard constraints, such as that the sensor nodes have to placed on a robot with such capabilities.
And this is done again using a PubSub communication platform (in our case Hazelcast), where nodes that were previously connected in the graph, must now communicate with intermediate topics.

And, of course, for this happen we need to serialize values of our Stream, keeping in mind that we should not throw an exception on serialization but rather materialize the stream on departure (that is transfer the complete/error signals as normal values) and de-materialize on arrival.

With these components in place, we can now say that our framework is heterogeneous.


ALGORITHMIC MUSIC
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
And now for something completely different!

So far we did boring stuff, robot controllers, hospitals....
so let's do something a bit more fun!

We will generate music using dataflow programming!

There is already a library that provides the necessary music datatypes, like `Note`, `Scale`, etc...
and in order to be able to use music-specific stream operators, we utilize Scala's implicit conversions feature, where you define a conversion between the imported `Stream` type and a more specialized version that only holds Music values, in which you can now define your domain-specific operators.

But how do we actually generate music? We are gonna use chaotic functions, which is a standard way to generate interesting music without using randomness.

The idea is very simple, a chaotic system is a set of recursive equations (called chaotic if it has a single variable, and complex otherwise) where you start with some initial values and recursively compute the next set of variables.

These systems typically have some parameters (alpha and beta in this example), and they are chaotic system because if you change the parameters or the initial values the output will change drastically.

We can express these systems quite naturally using our stream language, by just initiating the stream with you initial values and the make a feedback loop that recursively calculates the next values using your complex function.

So, let's the code!
We start with these interesting chaotic numeric sequences and then map them to notes and rhythms, constrained to a particular musical scale (in this case, Ab harmonic minor).

We produce two voices, one for the low register and one for the mid,
and assign an instrument to each of them. We can then write the output to a MIDI file, so let's listen to it.

To see a second example, we can also not constraint the notes in any particular to fully utililize the sound spectrum of the chaotic system.
So now, we see these lambdas that always return true which means we have no music-theoretic constraints on the output.
We also use non-typical instruments and apply some effects to get more interesting sounds. Let's see what *this* sounds like!

...It's weird but I like it.

We can now say that the system is extensible, since we managed to move to a completely different domain and use it there.

LIMITATIONS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
But, of course, there are limitations.

We saw that it is rather difficult to extend the language with domain-specific operators, and more importantly the programmer has more freedom than needed. For example, you could assign to a stream variable multiple times, but this doesn't make any sense.
Moreover, you always have a specific program structure:
- you start with the configuration of your strategies
- you then define a set of disjoint dataflow graphs
- and the function you pass as arguments to higher-order operators like map are, in principle, pure functions without side-effects.

FUTURE WORK
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
There are a lot of things for future work.
- Our optimizations are rather naive, and there is extensive literature on optimizing stream pipelines, so you could implement these ideas as another OptStrategy.
- Node place is currently rather primitive, but there has been recent research on using reinforcement learning to place sequence of operators to specific kinds of devices, by having the computation time as the reward.
- Another great feature that we do not currently support is dynamic reconfiguration, that is being able to how-swap different nodes of the dataflow without having to restart everything.
- As far as error-handling is concerned, we could certainly use a more Erland-style approach, where instead of just propagating errors through the streams, you also monitor certain nodes, and gracefully recover in case of an error.
- Of course, one could implement more backends, for example a TensorFlow one that converts our dataflow representation to the one TensorFlow uses, and then easily integrate in a robotics/IoT application.

ZIRIA
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
One last thing I want to mention is Ziria: a dataflow DSL for wireless systems programming, and more specifically software-defined radios.

What they manage to do, is define a highly declarative language with network-specific operators, that is then compiled to highly-optimized C code using vectorization.

And when they compared to an existing low-level C++ library, they saw that the code for certain task was significantly small (3000 cs 23000 lines of code), while keeping the performance the same!! (which is a great thing, right?)

CONCLUSION
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Because if we look at this pattern a bit more generally, we can see that there are always certain domains that are fixated on low-level techniques while the FP paradigm can nicely overcome this.

And if I want to get one point across in this talk, is that there are always such domains and always such obsolete low-level ways of doing things in it
and, in these cases, we should always strive for higher and higher abstractions.


QUESTIONS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
And that's all from me. Thank you!
