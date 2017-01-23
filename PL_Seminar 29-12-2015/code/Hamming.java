Stream.just(1).loop(entry -> mergeSort(
            mergeSort(
                    entry.map(i -> 2 * i),
                    entry.map(i -> 3 * i)
                ),
            entry.map(i -> 5 * i)
        )
    )
    .startWith(1)
    .subscribe(System.out::println);

Stream<Integer> mergeSort(Stream<Integer> s1, Stream<Integer> s2) {
    Queue<Integer> queue = new PriorityQueue<>();
    return Stream.zip(s1, s2, (i1, i2) -> {
        Integer min = Math.min(i1, i2), max = Math.max(i1, i2);
        queue.add(max);
        if (min < queue.peek())
            return min;
        else {
            queue.add(min);
            return queue.poll();
        }
    }).concatWith(Stream.from(queue));
}