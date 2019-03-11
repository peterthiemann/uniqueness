

type 'a pool =
  'a Queue.t * int * (unit -> 'a)
let create i spawn : _ pool =
  let q = Queue.create () in
  q, i, spawn


