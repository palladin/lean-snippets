

syntax:min "lazy" "(" term ")" : term
macro_rules
  | `(lazy ($x)) => `(Thunk.mk (fun () => $x))


#check lazy (1 + 1)
#check Thunk.get (lazy (1 + 1))
