
-- Bird's circular program

import Snippets.MyMacros

unsafe def fix : (Thunk α → α) → Thunk α :=
  fun f =>
    let rec loop := lazy (f loop)
    loop

unsafe def trace : (α → Thunk b → (c × b)) → α → c :=
  fun f x =>
    let r := fix (fun g => f x (g |>.map Prod.snd))
    r.get.fst


inductive Tree (α : Type u) : Type u
  | leaf : α → Tree α
  | branch : Tree α → Tree α → Tree α

def copy : Tree Nat → Thunk Nat → (Tree (Thunk Nat) × Nat) :=
  fun t thunk =>
    match t with
    | .leaf x => (.leaf thunk, x)
    | .branch l r =>
      let (tl, ml) := copy l thunk
      let (tr, mr) := copy r thunk
      (.branch tl tr, min ml mr)

unsafe def repmin : Tree Nat → Tree (Thunk Nat) :=
  fun t => trace copy t

def print : Tree (Thunk Nat) → String
  | .leaf x => s!"L {x.get}"
  | .branch l r => s!"(B {print l} {print r})"

def test : Tree Nat := .branch (.branch (.leaf 0) (.leaf 2)) (.leaf 1)

#eval test |> repmin |> print


-- Pettorossi's higher-order program

def repmin' : Tree Nat → Tree Nat :=
  fun t =>
    let rec aux : Tree Nat → ((Nat → Tree Nat) × Nat)
      | .leaf x => (fun m => .leaf m, x)
      | .branch l r =>
        let (fl, ml) := aux l
        let (fr, mr) := aux r
        (fun m => .branch (fl m) (fr m), min ml mr)

    let (f, m) := aux t
    f m

example : repmin' test = .branch (.branch (.leaf 0) (.leaf 0)) (.leaf 0) :=
  rfl
