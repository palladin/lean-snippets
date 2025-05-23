-- Based on "Using Circular Programs for Higher-Order Syntax"
-- [https://emilaxelsson.github.io/documents/axelsson2013using.pdf]

import Snippets.MyMacros

abbrev LazyName := Thunk Nat
abbrev Name := Nat

inductive Exp (α : Type u) : Type u
  | var : α → Exp α
  | app : Exp α → Exp α → Exp α
  | lam : α → Exp α → Exp α
deriving Repr

def maxBV : Exp LazyName → Name
    | .var _ => 0
    | .app f e => max (maxBV f) (maxBV e)
    | .lam n _ => n.get

unsafe def lam (f : Exp LazyName → Exp LazyName) : Exp LazyName :=
    let rec result : Exp LazyName × LazyName :=
      (lazy (result.snd.get) |> .var |> f, lazy (result.fst |> maxBV |> (· + 1)))
    .lam result.snd result.fst


def forceExp : Exp LazyName → Exp Name
  | .var n => n.get |> .var
  | .app f e => .app (forceExp f) (forceExp e)
  | .lam n body => .lam n.get (forceExp body)

unsafe def test : Exp LazyName :=
  lam (fun x => .app (.app (lam (fun y => y)) (lam (fun z => z))) x)


#eval test |> forceExp
