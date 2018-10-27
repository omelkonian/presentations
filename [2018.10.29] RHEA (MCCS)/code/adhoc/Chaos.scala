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
import rhea_music.constants.Chords._
import rhea_music.constants.Notes._
import rhea_music.constants.ScaleTypes._
import rhea_music.constants.Tones._
import rhea_music.constants.Octaves._
import rhea_music.constants.Durations._
import rhea_music.constants.NoteMods._
import rhea_music.constants.Instruments._

class Adhoc {

  @Before
  def setEval(): Unit = {
    Stream.evaluationStrategy = new RxjavaEvaluationStrategy
  }

  @Test
  def melodies(): Unit = {
    val sc = new Scale(Ab, harmonicMinor)

    // Chaotic sequences
    val Array(s1, s2) = ChaosStream.from(ComplexFunction.f3(1.4, .3))
    val Array(s3, s4) = ChaosStream.from(ComplexFunction.f3(1.42, .28))

    // Melody
    val melody = s1.mapTo[Note](constraintNotes(sc, mid))
                   .setDuration(s3.mapTo[Time](medium))
    // Bass
    val bass = s2.mapTo[Note](constraintNotes(sc, low))
                 .setDuration(s4.mapTo[Time](slow))

    (VIBRAPHONE |> melody || HARP |> bass)
    .writeMidi("duet")
  }

}
