
import Snippets.MyMacros

unsafe def sameObject : Bool :=
  let rec t : Thunk USize := lazy (ptrAddrUnsafe t)
  let p := ptrAddrUnsafe t
  let p' := t.get
  p == p'

#eval sameObject

unsafe def cachedTest : Bool :=
  let rec t : Thunk ((Unit → Nat) × Nat) := lazy (dbg_trace "In" ; ((fun () => t.get.snd), 42))
  let (f, v) := t.get
  f () == v

#eval cachedTest
