var time_previous: number | undefined
var timediffs: number[] = []

export function timestampBegin() {
  const time_now = (new Date()).getTime()
  time_previous = time_now
}

export function timestampEnd() {
  const time_now = (new Date()).getTime()
  if (time_previous === undefined) {
    throw Error("a `timediffstampEnd` called before a `timediffstampPrevious`")
  } else {
    timediffs.push(time_now - time_previous)
    time_previous = undefined
  }
}

export function logTimeDiffs() {
  console.log("==[ timediffs ]===============================")
  console.log(timediffs.reverse().join(", "))
}