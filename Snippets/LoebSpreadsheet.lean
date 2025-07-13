-- From Löb's Theorem to Spreadsheet Evaluation
-- based on http://blog.sigfpe.com/2006/11/from-l-theorem-to-spreadsheet.html

import Snippets.LazyStream

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
