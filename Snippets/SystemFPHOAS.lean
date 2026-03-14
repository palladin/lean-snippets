/-!
  # System F via Pure PHOAS

  An implementation of System F (the polymorphic lambda calculus) using
  Parametric Higher-Order Abstract Syntax, following the patterns from
  https://lean-lang.org/examples/1900-1-1-parametric-higherorder-abstract-syntax/

  Terms are intrinsically typed: `Term' rep ty` is indexed by the object-language
  type of the term. This file keeps the core syntax together with rendering and
  denotation.
-/

namespace SystemFPHOAS


inductive Ty' (tvar : Type _) : Type _ where
  | var : tvar -> Ty' tvar
  | fn : Ty' tvar -> Ty' tvar -> Ty' tvar
  | all : (tvar -> Ty' tvar) -> Ty' tvar

abbrev Ty := {tvar : Type _} -> Ty' tvar

namespace Ty'

def pretty (ty : Ty' String) (next : Nat := 0) : String :=
  match ty with
  | .var name => name
  | .fn dom cod => s!"({pretty dom next} -> {pretty cod next})"
  | .all body =>
      let name := s!"T{next}"
      s!"(forall {name}. {pretty (body name) (next + 1)})"

@[reducible] def denote : Ty' (Type v) -> Type (v + 1)
  | .var ty => ULift.{v + 1, v} ty
  | .fn dom ran => denote dom -> denote ran
  | .all body => (ty : Type v) -> denote (body ty)

end Ty'

def Ty.pretty (ty : Ty) : String :=
  Ty'.pretty (ty (tvar := String))

def Ty.denote (ty : Ty) : Type 1 :=
  Ty'.denote (ty (tvar := Type))

def idTy : Ty :=
  .all (fun ty => .fn (.var ty) (.var ty))

def composeTy : Ty :=
  .all (fun a =>
    .all (fun b =>
      .all (fun c =>
        .fn (.fn (.var b) (.var c))
          (.fn (.fn (.var a) (.var b))
            (.fn (.var a) (.var c))))))

def churchNatTy : Ty :=
  .all (fun a =>
    .fn (.fn (.var a) (.var a))
      (.fn (.var a) (.var a)))

def churchListBody {tvar : Type _} (a : tvar) : Ty' tvar :=
  .all (fun r =>
    .fn (.var r)
      (.fn (.fn (.var a) (.fn (.var r) (.var r)))
        (.var r)))

def churchListTy : Ty :=
  .all churchListBody

def churchSingletonTy : Ty :=
  .all (fun a =>
    .fn (.var a) (churchListBody a))

def churchPairTy : Ty :=
  .all (fun a =>
    .fn (.var a) (.fn (.var a) (churchListBody a)))

def churchListMapTy : Ty :=
  .all (fun a =>
    .all (fun b =>
      .fn (.fn (.var a) (.var b))
        (.fn (churchListBody a) (churchListBody b))))

inductive Term' {tvar : Type _} (rep : Ty' tvar -> Type _) : Ty' tvar -> Type _ where
  | var : rep ty -> Term' rep ty
  | lam : (rep dom -> Term' rep ran) -> Term' rep (.fn dom ran)
  | app : Term' rep (.fn dom ran) -> Term' rep dom -> Term' rep ran
  | tlam : ((ty : tvar) -> Term' rep (body ty)) -> Term' rep (.all body)
  | tapp : Term' rep (.all body) -> (ty : tvar) -> Term' rep (body ty)

abbrev Term (ty : Ty) := {tvar : Type _} -> {rep : Ty' tvar -> Type _} -> Term' rep (ty (tvar := tvar))

namespace Term'

def pretty {ty : Ty' String} (term : Term' (fun _ : Ty' String => String) ty)
    (nextTy : Nat := 0) (nextTm : Nat := 0) : String :=
  match term with
  | .var name => name
  | .lam body =>
    let name := s!"x{nextTm}"
    s!"(fun {name} => {pretty (body name) nextTy (nextTm + 1)})"
  | .app funTerm argTerm =>
    s!"({pretty funTerm nextTy nextTm} {pretty argTerm nextTy nextTm})"
  | .tlam body =>
    let name := s!"T{nextTy}"
    s!"(Lambda {name}. {pretty (body name) (nextTy + 1) nextTm})"
  | .tapp (body := body) funTerm tyArg =>
    let _ := body
    s!"({pretty funTerm nextTy nextTm} [{tyArg}])"

@[simp] def denote {ty : Ty' (Type v)} : Term' Ty'.denote ty -> Ty'.denote ty
  | .var x => x
  | .lam body => show Ty'.denote (.fn _ _) from fun x => denote (body x)
  | .app funTerm argTerm =>
    show Ty'.denote _ from (denote funTerm) (denote argTerm)
  | .tlam body => show Ty'.denote (.all _) from fun ty => denote (body ty)
  | .tapp (body := body) funTerm tyArg =>
    let _ := body
    show Ty'.denote _ from (denote funTerm) tyArg

end Term'

def Term.pretty (term : Term ty) : String :=
  let renderedTerm := Term'.pretty (term (tvar := String) (rep := fun _ => String))
  let renderedType := Ty.pretty ty
  s!"({renderedTerm} : {renderedType})"

def Term.denote (term : Term ty) : Ty.denote ty :=
  Term'.denote (term (tvar := Type) (rep := Ty'.denote))

def polyId : Term idTy :=
  .tlam (fun _ => .lam (fun x => .var x))

def polyConstTy : Ty :=
  .all (fun a =>
    .all (fun b =>
      .fn (.var a) (.fn (.var b) (.var a))))

def polyConst : Term polyConstTy :=
  .tlam (fun _ =>
    .tlam (fun _ =>
      .lam (fun x =>
        .lam (fun _ => .var x))))

def compose : Term composeTy :=
  .tlam (fun _ =>
    .tlam (fun _ =>
      .tlam (fun _ =>
        .lam (fun f =>
          .lam (fun g =>
            .lam (fun x =>
              .app (.var f) (.app (.var g) (.var x))))))))

def churchZero : Term churchNatTy :=
  .tlam (fun _ =>
    .lam (fun _ =>
      .lam (fun x =>
        .var x)))

def churchOne : Term churchNatTy :=
  .tlam (fun _ =>
    .lam (fun f =>
      .lam (fun x =>
        .app (.var f) (.var x))))

def churchTwo : Term churchNatTy :=
  .tlam (fun _ =>
    .lam (fun f =>
      .lam (fun x =>
        .app (.var f) (.app (.var f) (.var x)))))

def churchNil : Term churchListTy :=
  .tlam (fun _ =>
    .tlam (fun _ =>
      .lam (fun z =>
        .lam (fun _ =>
          .var z))))

def churchSingleton : Term churchSingletonTy :=
  .tlam (fun _ =>
    .lam (fun x =>
      .tlam (fun _ =>
        .lam (fun z =>
          .lam (fun cons =>
            .app (.app (.var cons) (.var x)) (.var z))))))

def churchPair : Term churchPairTy :=
  .tlam (fun _ =>
    .lam (fun x =>
      .lam (fun y =>
        .tlam (fun _ =>
          .lam (fun z =>
            .lam (fun cons =>
              .app (.app (.var cons) (.var x))
                (.app (.app (.var cons) (.var y)) (.var z))))))))

def churchListMap : Term churchListMapTy :=
  .tlam (fun a =>
    .tlam (fun _ =>
      .lam (fun f =>
        .lam (fun xs =>
          .tlam (fun r =>
            .lam (fun z =>
              .lam (fun cons =>
                let step : Term' _ (.fn (.var a) (.fn (.var r) (.var r))) :=
                  .lam (fun x =>
                    .lam (fun acc =>
                      .app
                        (.app (.var cons) (.app (.var f) (.var x)))
                        (.var acc)))
                .app
                  (.app (.tapp (.var xs) r) (.var z))
                  step)))))))

#check show (x : Type) → ULift x → ULift x from Term.denote polyId

#eval (Term.denote polyId) Nat ⟨3⟩
#eval (Term.denote polyConst) Nat Bool ⟨2⟩ ⟨true⟩
#eval (Term.denote compose) Nat Nat Nat (fun n => ⟨n.down + 1⟩) (fun n => ⟨n.down * 2⟩) ⟨10⟩
#eval (Term.denote churchZero) Nat (fun n => ⟨n.down + 1⟩) ⟨0⟩
#eval (Term.denote churchOne) Nat (fun n => ⟨n.down + 1⟩) ⟨0⟩
#eval (Term.denote churchTwo) Nat (fun n => ⟨n.down + 1⟩) ⟨0⟩
#eval (Term.denote churchNil) Nat Nat ⟨0⟩ (fun _ tail => tail)
#eval (Term.denote churchSingleton) Nat ⟨7⟩ Nat ⟨0⟩ (fun _ tail => ⟨tail.down + 1⟩)
#eval (Term.denote churchPair) Nat ⟨7⟩ ⟨11⟩ Nat ⟨0⟩ (fun _ tail => ⟨tail.down + 1⟩)
#eval (Term.denote churchListMap) Nat Nat (fun n => ⟨n.down + 10⟩)
  ((Term.denote churchPair) Nat ⟨7⟩ ⟨11⟩) Nat ⟨0⟩ (fun x tail => ⟨x.down + tail.down⟩)

#eval Ty.pretty idTy
#eval Ty.pretty composeTy
#eval Ty.pretty churchNatTy
#eval Ty.pretty churchListTy
#eval Ty.pretty churchSingletonTy
#eval Ty.pretty churchPairTy
#eval Ty.pretty churchListMapTy
#eval Term.pretty polyId
#eval Term.pretty polyConst
#eval Term.pretty compose
#eval Term.pretty churchZero
#eval Term.pretty churchOne
#eval Term.pretty churchTwo
#eval Term.pretty churchNil
#eval Term.pretty churchSingleton
#eval Term.pretty churchPair
#eval Term.pretty churchListMap

end SystemFPHOAS
