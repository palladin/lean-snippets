import Snippets.MyMacros
import Snippets.LazyStream

unsafe def fix : (Thunk α → α) → Thunk α :=
  fun f =>
    let rec x : Thunk α := lazy (f x)
    x

unsafe def fact : Thunk (Nat → Nat) → Nat → Nat :=
  fun rec n =>
    if n == 0 then 1 else n * rec.get (n - 1)

#eval fact |> fix |>.get |> (· 5)

unsafe def ones : Thunk (LazyStream Nat) :=
  fix (fun s => .cons (1 : Nat) s)

#eval ones.get |>.take 10
