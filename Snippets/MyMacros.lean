

syntax "lazy" "(" term ")" : term
macro_rules
  | `(lazy ($x)) => `(Thunk.mk (fun () => $x))


#check lazy (1 + 1)
