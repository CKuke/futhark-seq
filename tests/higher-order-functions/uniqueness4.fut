-- A partially applied function whose closure has been consumed.
-- ==
-- error: consumed

let const x _ = x[0]

let main(y: i32, QUUX: *[]i32) =
  let f = const QUUX
  let QUUX[1] = 2
  in f y
