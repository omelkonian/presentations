Stream
.just(0)
.loop(s -> s.map(i -> i + 1))
.subscribe(System::println);
