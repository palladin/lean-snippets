-- Based on "Using Circular Programs for Higher-Order Syntax"
-- [https://emilaxelsson.github.io/documents/axelsson2013using.pdf]

abbrev LazyName := Thunk Nat
abbrev Name := Nat

inductive Exp (a : Type u) : Type u
  | var : a → Exp a
  | app : Exp a → Exp a → Exp a
  | lam : a → Exp a → Exp a
deriving Repr

def maxBV : Exp LazyName → Name
    | .var _ => 0
    | .app f e => max (maxBV f) (maxBV e)
    | .lam n _ => n.get

unsafe def lam (f : Exp LazyName → Exp LazyName) : Exp LazyName :=
    let rec result : Exp LazyName × LazyName :=
      (f (.var (Thunk.mk (fun () => result.snd.get))), Thunk.mk (fun () => (maxBV result.fst) + 1))
    .lam result.snd result.fst


def forceExp : Exp LazyName → Exp Name
  | .var n => n.get |> .var
  | .app f e => .app (forceExp f) (forceExp e)
  | .lam n body => .lam n.get (forceExp body)

unsafe def test : Exp LazyName :=
  lam (fun x => .app (.app (lam (fun y => y)) (lam (fun z => z))) x)


#eval test |> forceExp
