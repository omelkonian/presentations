Topic myTopic = subscribe "sensor" >>> filter(> threshold)
Node actor = publish "cmd" (map act myTopic)