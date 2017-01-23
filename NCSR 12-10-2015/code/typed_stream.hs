Topic t :: Stream[Float]
Topic t = subscribe "sonar1" >>> filter(> 0)