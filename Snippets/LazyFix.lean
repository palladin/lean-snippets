import Snippets.MyMacros

unsafe def fix : (Thunk α → α) → Thunk α :=
  fun f =>
    let rec x : Thunk α := lazy (f x)
    x

unsafe def fact : Thunk (Nat → Nat) → Nat → Nat :=
  fun rec n =>
    if n == 0 then 1 else n * rec.get (n - 1)

#eval fact |> fix |>.get |> (· 5)


inductive LazyStream (α : Type u) : Type u where
  | cons : α → Thunk (LazyStream α) → LazyStream α

def LazyStream.take : Nat → LazyStream α → List α
  | 0,   _          => []
  | n+1, .cons h t => h :: LazyStream.take n t.get

unsafe def ones : Thunk (LazyStream Nat) :=
  fix (fun s => .cons 1 s)

#eval ones.get |>.take 10
