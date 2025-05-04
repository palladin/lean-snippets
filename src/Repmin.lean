
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
  | lead : a → Tree a
  | branch : Tree a → Tree a → Tree a

def copy : Tree Nat → Thunk Nat → (Tree (Thunk Nat) × Nat) :=
  fun t thunk =>
    match t with
    | .lead x => (.lead thunk, x)
    | .branch l r =>
      let (tl, ml) := copy l thunk
      let (tr, mr) := copy r thunk
      (.branch tl tr, min ml mr)

unsafe def repmin : Tree Nat → Tree (Thunk Nat) :=
  fun t => trace copy t

def print : Tree (Thunk Nat) → String
  | .lead x => s!"L {x.get}"
  | .branch l r => s!"(B {print l} {print r})"

def test : Tree Nat := .branch (.branch (.lead 0) (.lead 2)) (.lead 1)

#eval test |> repmin |> print



-- Pettorossi's higher-order program

def repmin' : Tree Nat → Tree Nat :=
  fun t =>
    let rec aux : Tree Nat → ((Nat → Tree Nat) × Nat)
      | .lead x => (fun m => .lead m, x)
      | .branch l r =>
        let (fl, ml) := aux l
        let (fr, mr) := aux r
        (fun m => .branch (fl m) (fr m), min ml mr)

    let (f, m) := aux t
    f m


example : repmin' (.branch (.branch (.lead 0) (.lead 2)) (.lead 1)) = .branch (.branch (.lead 0) (.lead 0)) (.lead 0) :=
  rfl
