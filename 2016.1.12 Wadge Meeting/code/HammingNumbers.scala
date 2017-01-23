class HammingNumbers extends StreamNode {
  override val name: String = "hamming_numbers"
  
  override def dataflow(): Unit =  {
    Stream.just(1)
          .loop(
            (entry: Stream[Int]) => 
            (entry.multiply(2) mergeSort entry.multiply(3)) 
              mergeSort  
              entry.multiply(5) : Stream[Int]
          )
          .startWith(1)
          .distinct
          .take(20)
          .subscribe((t: Int) => println(t))  
  }

  // Pimping library using "implicit conversions"  
  class RichStream(stream: Stream[Int]) {

    def multiply(constant: Int): Stream[Int] =
      stream.map((i: Int) => i * constant)

    def mergeSort(other: Stream[Int]): Stream[Int] = {
      val queue: java.util.Queue[Int] = new PriorityQueue[Int]()
      Stream.zip(stream, other, (i1: Int, i2: Int) => {
          val min: Int = Math.min(i1, i2)
          val max: Int = Math.max(i1, i2)
          queue.add(max)
          if (min < queue.peek())
            min
          else {
            queue.add(min)
            queue.poll()
          }
        }: Int)
        .concatWith(Stream.from(queue))
    }
  }
  implicit def enrichStream(st: Stream[Int]): RichStream = new RichStream(st)
}