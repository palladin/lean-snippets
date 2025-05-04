
-- Bird's circular program

unsafe def fix : (Thunk a → a) → Thunk a :=
  fun f =>
    let rec loop := Thunk.mk (fun () => f loop)
    loop

unsafe def trace : (a → Thunk b → (c × b)) → a → c :=
  fun f x =>
    let r := fix (fun g => f x (Thunk.map Prod.snd g))
    r |>.get |>.fst


inductive Tree (a : Type u) : Type u
  | Leaf : a → Tree a
  | Branch : Tree a → Tree a → Tree a

def copy : Tree Nat → Thunk Nat → (Tree (Thunk Nat) × Nat) :=
  fun t thunk =>
    match t with
    | .Leaf x => (.Leaf thunk, x)
    | .Branch l r =>
      let (tl, ml) := copy l thunk
      let (tr, mr) := copy r thunk
      (.Branch tl tr, min ml mr)

unsafe def repmin : Tree Nat → Tree (Thunk Nat) :=
  fun t => trace copy t

def print : Tree (Thunk Nat) → String
  | .Leaf x => s!"L {x.get}"
  | .Branch l r => s!"(B {print l} {print r})"

def test : Tree Nat := .Branch (.Branch (.Leaf 0) (.Leaf 2)) (.Leaf 1)

#eval test |> repmin |> print



-- Pettorossi's higher-order program

def repmin' : Tree Nat → Tree Nat :=
  fun t =>
    let rec aux : Tree Nat → ((Nat → Tree Nat) × Nat)
      | .Leaf x => (fun m => .Leaf m, x)
      | .Branch l r =>
        let (fl, ml) := aux l
        let (fr, mr) := aux r
        (fun m => .Branch (fl m) (fr m), min ml mr)

    let (f, m) := aux t
    f m


example : repmin' (.Branch (.Branch (.Leaf 0) (.Leaf 2)) (.Leaf 1)) = .Branch (.Branch (.Leaf 0) (.Leaf 0)) (.Leaf 0) :=
  rfl
