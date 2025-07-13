import Snippets.ContT

-- Based on http://www.madore.org/~david/programs/unlambda/

inductive Value where
  | Delay : Value
  | Func : (Dynamic → ContT Unit IO Dynamic) → Value
  deriving TypeName

def get : Dynamic → IO Value := fun d =>
  match d.get? Value with
  | .some r => pure r
  | .none => panic! "Invalid Value!"

def toValue : (Value → ContT Unit IO Value) → Value := fun k =>
  Value.Func (fun d => do
    let r ← get d
    let r' ← k r
    pure <| Dynamic.mk r')

def liftValue : (Value → ContT Unit IO Value) → ContT Unit IO Value := fun f => pure (toValue f)

inductive Expr where
  | s : Expr
  | k : Expr
  | i : Expr
  | r : Expr
  | c : Expr
  | d : Expr
  | dot : Char → Expr
  | backtick : Expr → Expr → Expr

def applyValue : Value → Value → ContT Unit IO Value := fun f arg => do
  match f with
  | Value.Func func => do
    let result ← func (Dynamic.mk arg)
    get result
  | Value.Delay =>
    pure arg

def apply : ContT Unit IO Value → ContT Unit IO Value → ContT Unit IO Value := fun first second => do
  let f ← first
  let s ← second
  applyValue f s

def eval : Expr → (Char → IO Unit) → ContT Unit IO Value := fun expr put =>
  match expr with
  | .s => liftValue (fun rec1 =>
               liftValue (fun rec2 =>
               liftValue (fun rec3 =>
               apply (apply (pure rec1) (pure rec3)) (apply (pure rec2) (pure rec3)))))
  | .k => liftValue (fun rec1 =>
               liftValue (fun _ => pure rec1))
  | .i => liftValue (fun rec => pure rec)
  | .r => liftValue (fun rec => do
               put '\n'
               pure rec)
  | .c => liftValue (fun rec => callCC (fun k => applyValue rec (toValue k)))
  | .d => pure Value.Delay
  | .dot char => liftValue (fun rec => do
               put char
               pure rec)
  | .backtick expr expr' => do
      let f ← eval expr put
      match f with
      | Value.Delay =>
          pure <| Value.Func (fun d => do
            let arg ← get d
            let func ← eval expr' put
            let result ← applyValue func arg
            pure (Dynamic.mk result))
      | _ =>
          let arg ← eval expr' put
          applyValue f arg

partial def parse : List Char → Option (Expr × List Char) := fun chars =>
  match chars with
  | 's' :: xs => some (.s, xs)
  | 'k' :: xs => some (.k, xs)
  | 'i' :: xs => some (.i, xs)
  | 'r' :: xs => some (.r, xs)
  | 'c' :: xs => some (.c, xs)
  | 'd' :: xs => some (.d, xs)
  | '.' :: c :: xs => some (.dot c, xs)
  | '`' :: xs => do
      let (expr, xs') ← parse xs
      let (expr', xs'') ← parse xs'
      some (.backtick expr expr', xs'')
  | _ :: _ => none
  | [] => none

def callCCTest : String :=
  "``cir"

def callCCNumbers : String :=
  "``r`ci`.*`ci"

def callCCInfinite : String :=
  "``cc`cc"

def helloWorldTest : String :=
  "```si`k``s.H``s.e``s.l``s.l``s.o``s. ``s.w``s.o``s.r``s.l``s.d``s.!``sri``si``si``si``si``si``si``si``si`ki"

def helloWorldInfinite : String :=
  "```s``sii`ki``s``s`ks``s``s`ks``s`k`s`kr``s`k`si``s`k`s`k`d````````````.H.e.l.l.o.,. .w.o.r.l.d.!kk`k``s``s`ksk`k.*"

def delayExample1 : String :=
  "``d`rii" -- prints a blank line

def delayExample2 : String :=
  "`id`ri" -- does not print a blank line

def testDD : String :=
  "```dd`.a.bi" -- ab

def runExample : String → IO Unit := fun program => do
  match parse program.data with
  | some (expr, _) => do
      run (fun _ => pure ()) (eval expr (fun c => IO.print c))
      pure ()
  | none => IO.println "Parse error"

def delayExample1Test : IO Unit := do
  IO.println "Running delay example 1..."
  runExample delayExample1

def delayExample2Test : IO Unit := do
  IO.println "Running delay example 2..."
  runExample delayExample2

def callCCTestExample : IO Unit := do
  IO.println "Running callCC test..."
  runExample callCCTest

def callCCNumbersExample : IO Unit := do
  IO.println "Running callCC numbers test..."
  runExample callCCNumbers

def callCCInfiniteExample : IO Unit := do
  IO.println "Running callCC infinite test..."
  runExample callCCInfinite

def helloWorldExample : IO Unit := do
  IO.println "Running hello world test..."
  runExample helloWorldTest

def helloWorldInfiniteExample : IO Unit := do
  IO.println "Running hello world infinite test..."
  runExample helloWorldInfinite

def testDDExample : IO Unit := do
  IO.println "Testing dd behavior..."
  runExample testDD

def main : List String → IO UInt32 := fun args => do
  match args with
  | [] => do
    IO.println "Usage: unlambda [test_name]"
    IO.println "Available tests:"
    IO.println "  dd          - Test dd behavior"
    IO.println "  delay1      - Test delay example 1"
    IO.println "  delay2      - Test delay example 2"
    IO.println "  callcc      - Test basic call/cc"
    IO.println "  callcc-nums - Test call/cc with numbers"
    IO.println "  callcc-inf  - Test call/cc infinite"
    IO.println "  hello       - Test hello world example"
    IO.println "  hello-inf   - Test hello world infinite example"
    IO.println "  all         - Run all tests"
    return 1
  | "dd" :: _ => do
    testDDExample
    return 0
  | "delay1" :: _ => do
    delayExample1Test
    return 0
  | "delay2" :: _ => do
    delayExample2Test
    return 0
  | "callcc" :: _ => do
    callCCTestExample
    return 0
  | "callcc-nums" :: _ => do
    callCCNumbersExample
    return 0
  | "callcc-inf" :: _ => do
    callCCInfiniteExample
    return 0
  | "hello" :: _ => do
    helloWorldExample
    return 0
  | "hello-inf" :: _ => do
    helloWorldInfiniteExample
    return 0
  | "all" :: _ => do
    testDDExample
    delayExample1Test
    delayExample2Test
    callCCTestExample
    callCCNumbersExample
    callCCInfiniteExample
    helloWorldExample
    helloWorldInfiniteExample
    return 0
  | test :: _ => do
    IO.println s!"Unknown test: {test}"
    IO.println "Use 'unlambda' with no arguments to see available tests"
    return 1
