type ('gstate, 'lstate, 'return) continuation =
  | Return of 'gstate * 'return
  | Continue of 'gstate * 'lstate

let bind f m =
  match m with Return (s, r) -> Return (s, r) | Continue (s, l) -> f s l

let map_gstate f m =
  match m with
  | Return (s, r) -> Return (f s, r)
  | Continue (s, l) -> Continue (f s, l)

let map_lstate f m =
  match m with Return _ -> m | Continue (s, l) -> Continue (s, f l)

let map_ret f m =
  match m with
  | Return (s, r) -> Return (s, f r)
  | Continue (s, l) -> Continue (s, l)

let ( >>= ) m f = bind f m
