-- Naperian Functors
-- Based on https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf


class Naperian (f : Type _ → Type _) extends Functor f where
  Log : Type _
  lookup : f α → (Log → α)
  positions : f Log
  tabulate : (Log → α) → f α


def Vector.lookup {α : Type} {n : Nat} (v : Vector α n) (i : Fin n) : α :=
  v.get i

def Vector.tabulate {α : Type} {n : Nat} (f : Fin n → α) : Vector α n :=
  Vector.ofFn f


instance : Functor (Vector · n) where
  map f v := Vector.map f v

instance (n : Nat) : Naperian (Vector · n) where
  Log := Fin n
  lookup := Vector.lookup
  tabulate := Vector.tabulate
  positions := Vector.tabulate id


def transpose [Naperian f] [Naperian g] (source : f (g α)) : g (f α) :=
  Naperian.tabulate fun j =>
    Naperian.tabulate fun i =>
      Naperian.lookup (Naperian.lookup source i) j

-- Examples
def testExample : Vector (Vector Int 3) 2 :=
  ⟨#[⟨#[1, 2, 3], rfl⟩, ⟨#[4, 5, 6], rfl⟩], rfl⟩

#eval transpose (f := (Vector · 2)) (g := (Vector · 3)) testExample
