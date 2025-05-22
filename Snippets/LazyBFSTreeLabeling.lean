import Snippets.MyMacros
import Snippets.LazyStreamModule

open LazyStream


inductive Tree (α : Type _) : Type _
  | leaf : α → Tree α
  | branch : Tree α → Tree α → Tree α

def treeMap : (α → β) → Tree α → Tree β := fun f t =>
  match t with
  | .leaf x => .leaf (f x)
  | .branch l r => .branch (treeMap f l) (treeMap f r)


def bfs : Tree Nat →  Thunk (LazyStream Nat) → Tree (Thunk Nat) × Thunk (LazyStream Nat) :=
  fun t s =>
    match t with
    | .leaf _ =>
        (.leaf <| lazy (s.get.head), lazy (.cons (lazy (s.get.head + 1)) s.get.tail))
    | .branch l r =>
        let (l', s') := bfs l <| lazy (s.get.tail.get)
        let (r', s'') := bfs r s'
        (.branch l' r', lazy (.cons (lazy (s.get.head)) s''))


unsafe def labelTree : Tree Nat → Tree Nat := fun t =>
  let rec result : Tree (Thunk Nat) × Thunk (LazyStream Nat) :=
    bfs t <| lazy (.cons (lazy (1)) result.snd)
  treeMap Thunk.get result.fst

-- Example tree structure:
--           Branch
--          /      \
--     Branch      Branch
--    /      \    /      \
-- Leaf(1) Branch Leaf(4) Leaf(5)
--        /      \
--    Leaf(2)  Leaf(3)

def exampleTree : Tree Nat :=
  .branch
    (.branch (.leaf 1) (.branch (.leaf 2) (.leaf 3)))
    (.branch (.leaf 4) (.leaf 5))


--           Branch
--          /      \
--     Branch      Branch
--    /      \    /      \
-- Leaf(1) Branch Leaf(2) Leaf(3)
--        /      \
--    Leaf(4)  Leaf(5)

#eval labelTree exampleTree
