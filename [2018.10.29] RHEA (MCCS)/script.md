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

- Sensor-based systems, such as robotics and IoT, are very naturally expressed as dataflow graphs, since you always have sensors that provide continuous streams of information that you process and transform in whatever way, eventually leading to an actuator that will perform actions on the output stream.

- Another application domain is Big Data, where you have enormous amount of continuous streams of information (think of tweets or click-streams) and you need to process them in a scalable and efficient manner. There are many dataflow frameworks, such as
  + Apache´s flink
  + Google´s map-reduce which is a degenerate form of a dataflow graph
  + and Microsoft's ReactiveExtensions which was actually developed by our very own Erik Meijer (I think he did a post-doc here, right?).

- We also see a lot of dataflow incluences in interactive systems, where you have to respond to user input such as UIs and games.
In the functional programming world, game libraries like Yampa embrace the FRP paradigm, which is very closely related with the dataflow model.

- And an example I should mention due to its high popularity,
is TensorFlow, a neural network construction library, where the user immediately writes dataflow graphs (representing neural-nets) and the backend then optimizes them, distibutes them over many devices, CUDA cores, and so forth...

MOTIVATION: ROBOTICS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
Diving a bit deeper in Robotics,

ROS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -


RHEA
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -


STREAM LANGUAGE
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

OPTIMIZATIONS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

APPLICATION: ROBOT PANEL
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

APPLICATION: ROBOT HOSPITAL GUIDE
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

DISTRIBUTION
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

ALGORITHMIC MUSIC
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

And now for something completely different!

So far we did boring stuff, robots, hospitals....
so let's do something a bit more fun!


LIMITATIONS/FUTURE WORK
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -


ZIRIA
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

CONCLUSION
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -


QUESTIONS
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
And that's all from me. Thank you!
