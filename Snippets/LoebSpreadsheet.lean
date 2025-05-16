import Snippets.MyMacros

inductive LazyStream (α : Type u) : Type u where
  | cons : Thunk α → Thunk (LazyStream α) → LazyStream α

def LazyStream.take : Nat → LazyStream α → List α
  | 0,   _          => []
  | n + 1, .cons h t => h.get :: LazyStream.take n t.get

def LazyStream.skip : Nat → LazyStream α → LazyStream α
  | 0, s => s
  | n + 1,  .cons _ t => skip n (t.get)

def LazyStream.head : LazyStream α → α
  | .cons h _ => h.get

def LazyStream.map : (α → β) → LazyStream α → LazyStream β := fun f s =>
  match s with
  | .cons h t => .cons (lazy (f h.get)) (lazy (map f t.get))

unsafe def LazyStream.replicate : α → LazyStream α := fun x => .cons x <| lazy (replicate x)

unsafe def LazyStream.ofList : α → List α → LazyStream α := fun d s =>
  match s with
  | [] => .replicate d
  | x :: xs => .cons x <| lazy (ofList d xs)

abbrev Cells α := LazyStream (LazyStream α)

unsafe def loeb : Cells (Cells α → α) → Cells α := fun cells =>
  let rec g : Cells α :=
    cells |>.map (fun fs => fs |>.map (fun f => f g))
  g

def nth : (Nat × Nat) → Cells Int → Int :=
  fun (i, j) cells => cells |>.skip i |>.head |>.skip j |>.head

def value : Int → Cells Int → Int := fun v _ => v

def emptyCell : Cells Int → Int := value 0
unsafe def emptyCells : LazyStream (Cells Int → Int) := .replicate (value 0)

unsafe def test : Cells (Cells Int → Int) :=
    [[value 1, nth (0, 0)],
     [value 2, fun c => nth (1, 0) c + nth (0, 1) c],
     [value 3, fun c => nth (2, 0) c + nth (1, 1) c],
     [value 4, fun c => nth (3, 0) c + nth (2, 1) c],
     [value 5, fun c => nth (4, 0) c + nth (3, 1) c]]
    |> List.map (LazyStream.ofList emptyCell) |> LazyStream.ofList emptyCells


#eval test |> loeb |>.take 5 |>.map (LazyStream.take 2)
