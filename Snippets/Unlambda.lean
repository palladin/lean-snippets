import Snippets.ContT

-- Based on http://www.madore.org/~david/programs/unlambda/

def Rec := Dynamic → ContT Unit IO Dynamic

deriving instance TypeName for Rec

def get : Dynamic → IO Rec := fun d =>
  match d.get? Rec with
  | .some r => pure r
  | .none => panic! "Invalid Rec!"

def toRec : (Rec → ContT Unit IO Rec) → Rec := fun k d => do
  let r ← get d
  let r' ← k r
  pure <| Dynamic.mk r'

def liftRec : (Rec → ContT Unit IO Rec) → ContT Unit IO Rec := fun f => f |> toRec |> pure

inductive Expr where
  | s : Expr
  | k : Expr
  | i : Expr
  | r : Expr
  | c : Expr
  | dot : Char → Expr
  | backtick : Expr → Expr → Expr

def apply : ContT Unit IO Rec → ContT Unit IO Rec → ContT Unit IO Rec := fun first second => do
  let f ← first
  let s ← second
  let result ← f (Dynamic.mk s)
  get result

def eval : Expr → (Char → IO Unit) → ContT Unit IO Rec := fun expr put =>
  match expr with
  | .s => liftRec (fun rec1 =>
               liftRec (fun rec2 =>
               liftRec (fun rec3 =>
               apply (apply (pure rec1) (pure rec3)) (apply (pure rec2) (pure rec3)))))
  | .k => liftRec (fun rec1 =>
               liftRec (fun _ => pure rec1))
  | .i => liftRec (fun rec => pure rec)
  | .r => liftRec (fun rec => do
               put '\n'
               pure rec)
  | .c => liftRec (fun rec => do
               callCC (fun k =>
                 k (fun _ => pure (Dynamic.mk rec))))
  | .dot char => liftRec (fun rec => do
               put char
               pure rec)
  | .backtick expr expr' => apply (eval expr put) (eval expr' put)

partial def parse : List Char → Option (Expr × List Char) := fun chars =>
  match chars with
  | 's' :: xs => some (.s, xs)
  | 'k' :: xs => some (.k, xs)
  | 'i' :: xs => some (.i, xs)
  | 'r' :: xs => some (.r, xs)
  | 'c' :: xs => some (.c, xs)
  | '.' :: c :: xs => some (.dot c, xs)
  | '`' :: xs => do
      let (expr, xs') ← parse xs
      let (expr', xs'') ← parse xs'
      some (.backtick expr expr', xs'')
  | _ :: _ => none
  | [] => none

def callCCTest : String :=
  "``cir"

def helloWorldTest : String :=
  "```si`k``s.H``s.e``s.l``s.l``s.o``s. ``s.w``s.o``s.r``s.l``s.d``s.!``sri``si``si``si``si``si``si``si``si`ki"


def runExample : IO Unit := do
  match parse helloWorldTest.data with
  | some (expr, _) => do
      run (fun _ => pure ()) (eval expr (fun c => IO.print c))
      pure ()
  | none => IO.println "Parse error"

def main : List String → IO UInt32 := fun _ => do
  IO.println "Testing Hello World:"
  runExample
  return 0
