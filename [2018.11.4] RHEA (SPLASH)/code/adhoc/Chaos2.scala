import org.junit.{Before, Test}

import scala.languageFeature.implicitConversions._
import scala_wrapper.ImplicitConversions._
import rhea_music.util.ImplicitConversions._

import org.rhea_core.Stream
import org.rhea_core.internal.graph.FlowGraph
import rhea_music.chaos.{ChaosStream, ChaoticFunction, ComplexFunction}
import rhea_music.music_streams.MusicStream
import rx_eval.RxjavaEvaluationStrategy
import test_data.utilities.Threads
import rhea_music.music_types.{Chord, Interval, Note, Scale}
import rhea_music.effects.{Sustain, Freeze}
import rhea_music.constants.Chords._
import rhea_music.constants.Notes._
import rhea_music.constants.ScaleTypes._
import rhea_music.constants.Tones._
import rhea_music.constants.Octaves._
import rhea_music.constants.Durations._
import rhea_music.constants.NoteMods._
import rhea_music.constants.Instruments._

class Adhoc2 {

  @Before
  def setEval(): Unit = {
    Stream.evaluationStrategy = new RxjavaEvaluationStrategy
  }

  @Test
  def melodies(): Unit = {
    // Chaotic sequences
    val Array(s1, s2) = ChaosStream.from(ComplexFunction.f3(1.4, .3))
    val Array(s3, s4) = ChaosStream.from(ComplexFunction.f3(1.42, .28))

    (  METALLIC |>
          s1.mapTo[Note](_ => true).setDuration(s2.mapTo[Time](_ => true))
    || BOWED |>
          s3.mapTo[Note](_ => true).setDuration(s4.mapTo[Time](_ => true))
    )
    .addEffects(Sustain >>> Freeze)
    .writeAudio("noise")
  }

}
