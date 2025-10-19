/-!
  # Little Scheme
  Minimal Scheme interpreter for "The Little Schemer"

  Architecture: Text → Tokens → SExpr → Expr → Value
  Special forms: quote, lambda, if, cond, define, let
  Primitives: +, -, *, =, <, >, car, cdr, cons, null?, atom?, eq?, zero?, number?, add1, sub1, list
-/

namespace LittleScheme

inductive Atom where
  | num : Int → Atom
  | sym : String → Atom
  | bool : Bool → Atom
  deriving Repr, BEq

inductive SExpr where
  | atom : Atom → SExpr
  | cons : SExpr → SExpr → SExpr
  | nil : SExpr
  deriving Repr, BEq

def SExpr.num (n : Int) : SExpr := SExpr.atom (Atom.num n)
def SExpr.sym (s : String) : SExpr := SExpr.atom (Atom.sym s)
def SExpr.bool (b : Bool) : SExpr := SExpr.atom (Atom.bool b)

inductive Expr where
  | lit : SExpr → Expr
  | var : String → Expr
  | quote : SExpr → Expr
  | lambda : List String → Expr → Expr
  | ifExpr : Expr → Expr → Expr → Expr
  | cond : List (Expr × Expr) → Expr
  | letExpr : List (String × Expr) → Expr → Expr
  | define : String → Expr → Expr
  | defineFunc : String → List String → Expr → Expr
  | primAdd : List Expr → Expr
  | primSub : List Expr → Expr
  | primMul : List Expr → Expr
  | primEq : Expr → Expr → Expr
  | primLt : Expr → Expr → Expr
  | primGt : Expr → Expr → Expr
  | primCar : Expr → Expr
  | primCdr : Expr → Expr
  | primCons : Expr → Expr → Expr
  | primNullQ : Expr → Expr
  | primAtomQ : Expr → Expr
  | primEqQ : Expr → Expr → Expr
  | primZeroQ : Expr → Expr
  | primNumberQ : Expr → Expr
  | primAdd1 : Expr → Expr
  | primSub1 : Expr → Expr
  | primList : List Expr → Expr
  | app : Expr → List Expr → Expr
  deriving Repr

def car : SExpr → Except String SExpr
  | .cons head _ => pure head
  | _ => throw "car: expected a pair"

def cdr : SExpr → Except String SExpr
  | .cons _ tail => pure tail
  | _ => throw "cdr: expected a pair"

def isNull : SExpr → Bool | .nil => true | _ => false
def isAtom : SExpr → Bool | .atom _ => true | .nil => true | _ => false

def sexprToList : SExpr → Option (List SExpr)
  | .nil => some []
  | .cons head tail => do let rest ← sexprToList tail; pure (head :: rest)
  | _ => none

def listToSexpr : List SExpr → SExpr | [] => .nil | x :: xs => .cons x (listToSexpr xs)

def SExpr.toString : SExpr → String
  | .atom (.num n) => s!"{n}"
  | .atom (.sym s) => s
  | .atom (.bool true) => "#t"
  | .atom (.bool false) => "#f"
  | .nil => "()"
  | .cons head tail =>
    let rec toStringList : SExpr → String
      | .nil => ""
      | .cons h t => s!" {h.toString}{toStringList t}"
      | e => s!" . {e.toString}"
    s!"({head.toString}{toStringList tail})"

instance : ToString SExpr where toString := SExpr.toString

inductive Value where
  | sexpr : SExpr → Value
  | closure : List String → Expr → List (String × Value) → Value
  | definition : String → Value → Value

abbrev Env := List (String × Value)

def Env.lookup (env : Env) (name : String) : Except String Value :=
  match env.find? (·.1 == name) with
  | some (_, val) => pure val
  | none => throw s!"Unbound variable: {name}"

def Env.extend (env : Env) (bindings : List (String × Value)) : Env :=
  bindings ++ env

def Env.empty : Env := []

def Value.toString : Value → String
  | .sexpr e => e.toString
  | .closure params _ _ => s!"<closure ({String.intercalate " " params})>"
  | .definition name _ => s!"<defined {name}>"

instance : ToString Value where toString := Value.toString

inductive Token where | lparen | rparen | quote | atom : String → Token

def tokenize (s : String) : List Token :=
  let rec aux (chars : List Char) (acc : List Token) (current : String) : List Token :=
    match chars with
    | [] => if current.isEmpty then acc.reverse else (Token.atom current :: acc).reverse
    | c :: rest =>
      if c.isWhitespace then
        if current.isEmpty then aux rest acc "" else aux rest (Token.atom current :: acc) ""
      else if c == '(' then
        if current.isEmpty then aux rest (Token.lparen :: acc) ""
        else aux rest (Token.lparen :: Token.atom current :: acc) ""
      else if c == ')' then
        if current.isEmpty then aux rest (Token.rparen :: acc) ""
        else aux rest (Token.rparen :: Token.atom current :: acc) ""
      else if c == '\'' then
        if current.isEmpty then aux rest (Token.quote :: acc) ""
        else aux rest (Token.quote :: Token.atom current :: acc) ""
      else aux rest acc (current.push c)
  aux s.toList [] ""

def parseAtom (s : String) : SExpr :=
  if s == "#t" then .bool true
  else if s == "#f" then .bool false
  else if s == "-" || s == "+" || s == "*" then .sym s
  else match s.toInt? with | some n => .num n | none => .sym s

inductive ParseFrame where
  | listFrame : List SExpr → ParseFrame
  | quoteFrame : ParseFrame

def handleCompleted (expr : SExpr) : List ParseFrame → Except String (Option SExpr × List ParseFrame)
  | [] => pure (some expr, [])
  | .quoteFrame :: rest =>
      handleCompleted (listToSexpr [SExpr.sym "quote", expr]) rest
  | .listFrame elems :: rest =>
    pure (none, .listFrame (expr :: elems) :: rest)

def parseTokensProcess : List Token → List ParseFrame → Except String (SExpr × List Token)
  | [], _ => throw "Unexpected end of input"
  | tok :: rest, stack =>
    match tok with
    | Token.lparen =>
      parseTokensProcess rest (.listFrame [] :: stack)
    | Token.rparen =>
      match stack with
      | [] => throw "Unexpected ')'"
      | frame :: stackTail =>
        match frame with
        | .quoteFrame => throw "quote: expected expression"
        | .listFrame elems => do
          let listExpr := listToSexpr (elems.reverse)
          match ← handleCompleted listExpr stackTail with
          | (some result, _) => pure (result, rest)
          | (none, newStack) => parseTokensProcess rest newStack
    | Token.quote =>
      parseTokensProcess rest (.quoteFrame :: stack)
    | Token.atom s => do
      let atomExpr := parseAtom s
      match ← handleCompleted atomExpr stack with
      | (some result, _) => pure (result, rest)
      | (none, newStack) => parseTokensProcess rest newStack

def parseTokens (tokens : List Token) : Except String (SExpr × List Token) :=
  parseTokensProcess tokens []

def parse (s : String) : Except String SExpr := do
  let (expr, _) ← parseTokens (tokenize s)
  pure expr

mutual
  def sexprToExpr (e : SExpr) : Except String Expr :=
    match e with
    | .atom (.num n) => pure (.lit (.num n))
    | .atom (.bool b) => pure (.lit (.bool b))
    | .atom (.sym s) => pure (.var s)
    | .nil => pure (.lit .nil)
    | .cons (.atom (.sym "quote")) (.cons arg .nil) => pure (.quote arg)
    | .cons (.atom (.sym "lambda")) (.cons params (.cons body .nil)) => do
      let ps ← match sexprToList params with | some lst => pure lst | none => throw "lambda: bad params"
      let names ← ps.mapM fun p => match p with | .atom (.sym s) => pure s | _ => throw "lambda: param names"
      let bodyExpr ← sexprToExpr body
      pure (.lambda names bodyExpr)
    | .cons (.atom (.sym "if")) (.cons test (.cons conseq (.cons alt .nil))) => do
      let testExpr ← sexprToExpr test
      let conseqExpr ← sexprToExpr conseq
      let altExpr ← sexprToExpr alt
      pure (.ifExpr testExpr conseqExpr altExpr)
    | .cons (.atom (.sym "cond")) clauses => do
      let pairs ← sexprListToCondClauses clauses
      pure (.cond pairs)
    | .cons (.atom (.sym "let")) (.cons bindings (.cons body .nil)) => do
      let pairs ← sexprListToLetBindings bindings
      let bodyExpr ← sexprToExpr body
      pure (.letExpr pairs bodyExpr)
    | .cons (.atom (.sym "define")) (.cons (.atom (.sym name)) (.cons valExpr .nil)) => do
      let e ← sexprToExpr valExpr
      pure (.define name e)
    | .cons (.atom (.sym "define")) (.cons (.cons (.atom (.sym name)) params) (.cons body .nil)) => do
      let ps ← match sexprToList params with | some lst => pure lst | none => throw "define: bad params"
      let names ← ps.mapM fun p => match p with | .atom (.sym s) => pure s | _ => throw "define: param names"
      let bodyExpr ← sexprToExpr body
      pure (.defineFunc name names bodyExpr)
    | .cons (.atom (.sym "+")) args => do
      let exprs ← sexprListToExprList args
      pure (.primAdd exprs)
    | .cons (.atom (.sym "-")) args => do
      let exprs ← sexprListToExprList args
      pure (.primSub exprs)
    | .cons (.atom (.sym "*")) args => do
      let exprs ← sexprListToExprList args
      pure (.primMul exprs)
    | .cons (.atom (.sym "=")) (.cons a (.cons b .nil)) => do
      let ea ← sexprToExpr a
      let eb ← sexprToExpr b
      pure (.primEq ea eb)
    | .cons (.atom (.sym "<")) (.cons a (.cons b .nil)) => do
      let ea ← sexprToExpr a
      let eb ← sexprToExpr b
      pure (.primLt ea eb)
    | .cons (.atom (.sym ">")) (.cons a (.cons b .nil)) => do
      let ea ← sexprToExpr a
      let eb ← sexprToExpr b
      pure (.primGt ea eb)
    | .cons (.atom (.sym "car")) (.cons a .nil) => do
      let ea ← sexprToExpr a
      pure (.primCar ea)
    | .cons (.atom (.sym "cdr")) (.cons a .nil) => do
      let ea ← sexprToExpr a
      pure (.primCdr ea)
    | .cons (.atom (.sym "cons")) (.cons a (.cons b .nil)) => do
      let ea ← sexprToExpr a
      let eb ← sexprToExpr b
      pure (.primCons ea eb)
    | .cons (.atom (.sym "null?")) (.cons a .nil) => do
      let ea ← sexprToExpr a
      pure (.primNullQ ea)
    | .cons (.atom (.sym "atom?")) (.cons a .nil) => do
      let ea ← sexprToExpr a
      pure (.primAtomQ ea)
    | .cons (.atom (.sym "eq?")) (.cons a (.cons b .nil)) => do
      let ea ← sexprToExpr a
      let eb ← sexprToExpr b
      pure (.primEqQ ea eb)
    | .cons (.atom (.sym "zero?")) (.cons a .nil) => do
      let ea ← sexprToExpr a
      pure (.primZeroQ ea)
    | .cons (.atom (.sym "number?")) (.cons a .nil) => do
      let ea ← sexprToExpr a
      pure (.primNumberQ ea)
    | .cons (.atom (.sym "add1")) (.cons a .nil) => do
      let ea ← sexprToExpr a
      pure (.primAdd1 ea)
    | .cons (.atom (.sym "sub1")) (.cons a .nil) => do
      let ea ← sexprToExpr a
      pure (.primSub1 ea)
    | .cons (.atom (.sym "list")) args => do
      let exprs ← sexprListToExprList args
      pure (.primList exprs)
    | .cons fn args => do
      let fnExpr ← sexprToExpr fn
      let argExprs ← sexprListToExprList args
      pure (.app fnExpr argExprs)

  -- Convert an SExpr list structure to a List of Exprs
  def sexprListToExprList : SExpr → Except String (List Expr)
    | .nil => pure []
    | .cons head tail => do
      let headExpr ← sexprToExpr head
      let tailExprs ← sexprListToExprList tail
      pure (headExpr :: tailExprs)
    | _ => throw "expected list"

  -- Convert an SExpr list structure to cond clauses
  def sexprListToCondClauses : SExpr → Except String (List (Expr × Expr))
    | .nil => pure []
    | .cons (.cons (.atom (.sym "else")) (.cons expr .nil)) tail => do
      let e ← sexprToExpr expr
      let rest ← sexprListToCondClauses tail
      pure ((.lit (.bool true), e) :: rest)
    | .cons (.cons test (.cons expr .nil)) tail => do
      let t ← sexprToExpr test
      let e ← sexprToExpr expr
      let rest ← sexprListToCondClauses tail
      pure ((t, e) :: rest)
    | .cons _ _ => throw "cond: bad clause"
    | _ => throw "cond: bad clauses"

  -- Convert an SExpr list structure to let bindings
  def sexprListToLetBindings : SExpr → Except String (List (String × Expr))
    | .nil => pure []
    | .cons (.cons (.atom (.sym name)) (.cons valExpr .nil)) tail => do
      let e ← sexprToExpr valExpr
      let rest ← sexprListToLetBindings tail
      pure ((name, e) :: rest)
    | .cons _ _ => throw "let: binding format"
    | _ => throw "let: bad bindings"
end

def parseExpr (s : String) : Except String Expr := do
  let sexpr ← parse s
  sexprToExpr sexpr

def defaultFuel : Nat := 10000

def evalCore : Nat → Env → Expr → Except String Value
  | 0, _, _ => throw "out of fuel"
  | Nat.succ fuel, env, expr =>
    match expr with
    | .lit sexpr => pure (.sexpr sexpr)
    | .var name => Env.lookup env name
    | .quote sexpr => pure (.sexpr sexpr)
    | .lambda params body => pure (.closure params body env)
    | .ifExpr test conseq alt => do
      match ← evalCore fuel env test with
      | .sexpr (.atom (.bool false)) => evalCore fuel env alt
      | _ => evalCore fuel env conseq
    | .cond clauses =>
      let rec evalCond : List (Expr × Expr) → Except String Value
        | [] => throw "cond: no match"
        | (test, result) :: rest => do
          match ← evalCore fuel env test with
          | .sexpr (.atom (.bool false)) => evalCond rest
          | _ => evalCore fuel env result
      evalCond clauses
    | .letExpr bindings body => do
      let vals ← bindings.mapM fun (_, expr) => evalCore fuel env expr
      let newBindings := bindings.map (·.1) |>.zip vals
      evalCore fuel (Env.extend env newBindings) body
    | .define name valExpr => do
      let val ← evalCore fuel env valExpr
      pure (.definition name val)
    | .defineFunc name params body =>
      let val := Value.closure params body env
      pure (.definition name val)
    | .primAdd exprs => do
      let vals ← exprs.mapM (evalCore fuel env)
      let nums ← vals.mapM fun v =>
        match v with
        | .sexpr (.atom (.num n)) => pure n
        | _ => throw "+: nums"
      pure (.sexpr (.num (nums.foldl (· + ·) 0)))
    | .primSub exprs => do
      match exprs with
      | [] => throw "-: need args"
      | [x] =>
        match ← evalCore fuel env x with
        | .sexpr (.atom (.num n)) => pure (.sexpr (.num (-n)))
        | _ => throw "-: num"
      | x :: xs => do
        match ← evalCore fuel env x with
        | .sexpr (.atom (.num n)) => do
          let rest ← xs.mapM (evalCore fuel env)
          let nums ← rest.mapM fun v =>
            match v with
            | .sexpr (.atom (.num m)) => pure m
            | _ => throw "-: nums"
          pure (.sexpr (.num (nums.foldl (· - ·) n)))
        | _ => throw "-: num"
    | .primMul exprs => do
      let vals ← exprs.mapM (evalCore fuel env)
      let nums ← vals.mapM fun v =>
        match v with
        | .sexpr (.atom (.num n)) => pure n
        | _ => throw "*: nums"
      pure (.sexpr (.num (nums.foldl (· * ·) 1)))
    | .primEq a b => do
      match ← evalCore fuel env a, ← evalCore fuel env b with
      | .sexpr (.atom (.num n1)), .sexpr (.atom (.num n2)) =>
        pure (.sexpr (.bool (n1 == n2)))
      | _, _ => throw "=: nums"
    | .primLt a b => do
      match ← evalCore fuel env a, ← evalCore fuel env b with
      | .sexpr (.atom (.num n1)), .sexpr (.atom (.num n2)) =>
        pure (.sexpr (.bool (n1 < n2)))
      | _, _ => throw "<: nums"
    | .primGt a b => do
      match ← evalCore fuel env a, ← evalCore fuel env b with
      | .sexpr (.atom (.num n1)), .sexpr (.atom (.num n2)) =>
        pure (.sexpr (.bool (n1 > n2)))
      | _, _ => throw ">: nums"
    | .primCar a => do
      match ← evalCore fuel env a with
      | .sexpr e =>
        match car e with
        | .ok result => pure (.sexpr result)
        | .error msg => throw msg
      | _ => throw "car: sexpr"
    | .primCdr a => do
      match ← evalCore fuel env a with
      | .sexpr e =>
        match cdr e with
        | .ok result => pure (.sexpr result)
        | .error msg => throw msg
      | _ => throw "cdr: sexpr"
    | .primCons a b => do
      match ← evalCore fuel env a, ← evalCore fuel env b with
      | .sexpr ea, .sexpr eb => pure (.sexpr (.cons ea eb))
      | _, _ => throw "cons: sexprs"
    | .primList exprs => do
      let vals ← exprs.mapM (evalCore fuel env)
      let sexprs ← vals.mapM fun v =>
        match v with
        | .sexpr e => pure e
        | _ => throw "list: sexprs"
      pure (.sexpr (listToSexpr sexprs))
    | .primNullQ a => do
      match ← evalCore fuel env a with
      | .sexpr e => pure (.sexpr (.bool (isNull e)))
      | _ => throw "null?: sexpr"
    | .primAtomQ a => do
      match ← evalCore fuel env a with
      | .sexpr e => pure (.sexpr (.bool (isAtom e)))
      | _ => throw "atom?: sexpr"
    | .primEqQ a b => do
      match ← evalCore fuel env a, ← evalCore fuel env b with
      | .sexpr ea, .sexpr eb => pure (.sexpr (.bool (ea == eb)))
      | _, _ => throw "eq?: sexprs"
    | .primZeroQ a => do
      match ← evalCore fuel env a with
      | .sexpr (.atom (.num 0)) => pure (.sexpr (.bool true))
      | .sexpr (.atom (.num _)) => pure (.sexpr (.bool false))
      | _ => throw "zero?: num"
    | .primNumberQ a => do
      match ← evalCore fuel env a with
      | .sexpr (.atom (.num _)) => pure (.sexpr (.bool true))
      | .sexpr _ => pure (.sexpr (.bool false))
      | _ => throw "number?: sexpr"
    | .primAdd1 a => do
      match ← evalCore fuel env a with
      | .sexpr (.atom (.num n)) => pure (.sexpr (.num (n + 1)))
      | _ => throw "add1: num"
    | .primSub1 a => do
      match ← evalCore fuel env a with
      | .sexpr (.atom (.num n)) => pure (.sexpr (.num (n - 1)))
      | _ => throw "sub1: num"
    | .app fnExpr argExprs => do
      let fn ← evalCore fuel env fnExpr
      let argVals ← argExprs.mapM (evalCore fuel env)
      match fn with
      | .closure params body closureEnv =>
        if params.length != argVals.length then
          throw s!"arity mismatch"
        else
          let mergedEnv := Env.extend env closureEnv
          evalCore fuel (Env.extend mergedEnv (params.zip argVals)) body
      | _ => throw "not a function"

def eval (env : Env) (expr : Expr) (fuel : Nat := defaultFuel) : Except String Value :=
  evalCore fuel env expr

def initialEnv : Env := Env.empty

def evalString (s : String) (fuel : Nat := defaultFuel) : Except String Value := do
  let expr ← parseExpr s
  eval initialEnv expr (fuel := fuel)

def evalProgram (env : Env) (exprs : List Expr) (fuel : Nat := defaultFuel) : Except String (Env × Value) :=
  match exprs with
  | [] => throw "empty program"
  | [expr] => do
    let val ← eval env expr (fuel := fuel)
    match val with
    | .definition name defVal =>
      let fixedVal := match defVal with
        | .closure params body closureEnv => .closure params body ((name, defVal) :: closureEnv)
        | _ => defVal
      let newEnv := Env.extend env [(name, fixedVal)]
      pure (newEnv, .definition name fixedVal)
    | _ => pure (env, val)
  | expr :: rest => do
    let val ← eval env expr (fuel := fuel)
    match val with
    | .definition name defVal =>
      let fixedVal := match defVal with
        | .closure params body closureEnv => .closure params body ((name, defVal) :: closureEnv)
        | _ => defVal
      evalProgram (Env.extend env [(name, fixedVal)]) rest (fuel := fuel)
    | _ => evalProgram env rest (fuel := fuel)

def evalProgramString (s : String) (fuel : Nat := defaultFuel) : Except String Value := do
  let tokens := tokenize s
  let rec parseAll (fuel : Nat) (ts : List Token) (acc : List SExpr) : Except String (List SExpr) :=
    match fuel with
    | 0 => throw "out of fuel"
    | Nat.succ fuel =>
      if ts.isEmpty then
        pure acc.reverse
      else do
        let (expr, rest) ← parseTokens ts
        parseAll fuel rest (expr :: acc)
  let sexprs ← parseAll (tokens.length.succ) tokens []
  if sexprs.isEmpty then throw "no expressions"
  let exprs ← sexprs.mapM sexprToExpr
  let (_, result) ← evalProgram initialEnv exprs (fuel := fuel)
  pure result

def test (name : String) (input : String) (expected : String) : IO Unit := do
  IO.println s!"Test: {name}"
  match evalString input with
  | .ok result =>
    if result.toString == expected then
      IO.println s!"  ✓ {result}"
    else
      IO.println s!"  ✗ got {result}, expected {expected}"
  | .error msg =>
    IO.println s!"  ✗ Error: {msg}"

def testProgram (name : String) (input : String) (expected : String) : IO Unit := do
  IO.println s!"Test: {name}"
  match evalProgramString input with
  | .ok result =>
    if result.toString == expected then
      IO.println s!"  ✓ {result}"
    else
      IO.println s!"  ✗ got {result}, expected {expected}"
  | .error msg =>
    IO.println s!"  ✗ Error: {msg}"

def runTests : IO Unit := do
  IO.println "=== Little Scheme Tests ===\n"
  test "number" "42" "42"
  test "bool" "#t" "#t"
  test "quote" "'hello" "hello"
  test "quote list" "'(1 2 3)" "(1 2 3)"
  test "add" "(+ 1 2 3)" "6"
  test "sub" "(- 10 3)" "7"
  test "mul" "(* 2 3 4)" "24"
  test "car" "(car '(1 2 3))" "1"
  test "cdr" "(cdr '(1 2 3))" "(2 3)"
  test "cons" "(cons 1 '(2 3))" "(1 2 3)"
  test "null?" "(null? '())" "#t"
  test "zero?" "(zero? 0)" "#t"
  test "=" "(= 5 5)" "#t"
  test "<" "(< 3 5)" "#t"
  test "if" "(if #t 1 2)" "1"
  test "cond" "(cond (#f 1) (else 2))" "2"
  test "lambda" "((lambda (x) (+ x 1)) 5)" "6"
  test "lambda 2" "((lambda (x y) (+ x y)) 3 4)" "7"
  test "closure" "((lambda (x) ((lambda (y) (+ x y)) 3)) 4)" "7"
  test "let" "(let ((x 5) (y 3)) (+ x y))" "8"
  test "let nested" "(let ((x 5)) (let ((y 3)) (+ x y)))" "8"
  testProgram "define var" "(define x 10) x" "10"
  testProgram "define func" "(define (square x) (* x x)) (square 5)" "25"
  testProgram "define recursive" "(define (fact n) (if (= n 0) 1 (* n (fact (- n 1))))) (fact 5)" "120"
  IO.println "\n✅ Tests complete!"

end LittleScheme

#eval LittleScheme.runTests
