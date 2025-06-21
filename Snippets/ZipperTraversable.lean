-- http://okmij.org/ftp/continuations/zipper.html#traversable

import Snippets.ContT
import Snippets.Classes


inductive Zipper (t : Type _ → Type _) (α : Type _) where
  | done : t α → Zipper t α
  | step : α → (Option α → Zipper t α) → Zipper t α


def maybe : α → Option α → (α → α) → α :=
  fun a o f =>
    match o with
    | .none   => a
    | .some a => f a

def makeZipper : [Traversable t] → t α → Zipper t α :=
  fun tr =>
    let f : α → Cont (Zipper t α) α := fun a =>
      shift (fun k => pure (.step a (fun o => k (maybe a o id))))
    let scope : Cont (Zipper t α) (Zipper t α) := do
      let x ← Traversable.traverse f tr
      pure (.done x)
    reset (m := Id) scope


def update : Zipper List Nat → List Nat :=
  fun z =>
    let rec go : Zipper List Nat → List Nat
      | .done xs => xs
      | .step x f => go (f (some (x + 1)))
    go z


#eval update (makeZipper [1, 2, 3, 4, 5])
