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

def LazyStream.tail : LazyStream α → Thunk (LazyStream α)
  | .cons _ t => t

def LazyStream.map : (α → β) → LazyStream α → LazyStream β := fun f s =>
  match s with
  | .cons h t => .cons (lazy (f h.get)) (lazy (map f t.get))


unsafe def unfold : (α → (β × α)) → α → LazyStream β
  | f, x =>
    let (y, next) := f x
    .cons y (lazy (unfold f next))

unsafe def LazyStream.replicate : α → LazyStream α := fun x =>
  unfold (fun x => (x, x)) x

unsafe def LazyStream.ofList : α → List α → LazyStream α := fun d s =>
  match s with
  | [] => .replicate d
  | x :: xs => .cons x <| lazy (ofList d xs)
