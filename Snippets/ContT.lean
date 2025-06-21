
def ContT (ω : Type _) (m : Type _ → Type _) (α : Type _) := (α → m ω) → m ω

abbrev Cont (ω : Type _) (α : Type _) := ContT ω Id α

def ContT.map : (α → β) → ContT ω m α → ContT ω m β := fun f c =>
  fun k => c (fun a => k (f a))

def ContT.pure : α → ContT ω m α := fun a k => k a
def ContT.bind : ContT ω m α → (α → ContT ω m β) → ContT ω m β := fun c f =>
  fun k => c (fun a => f a k)
def ContT.lift : [Monad m] → m α → ContT ω m α := fun c k => do
    let x ← c
    k x

instance : Functor (ContT ω m) where
  map f c := .map f c

instance : Applicative (ContT ω m) where
  pure := .pure
  seq c f := fun k => c (fun a => f () (fun b => k (a b)))

instance : Monad (ContT ω m) where
  bind := .bind

instance [Monad m] : MonadLift m (ContT ω m) where
  monadLift := .lift


def run : (α → m ω) → ContT ω m α → m ω := fun k c => c k

def reset : [Monad m] → ContT ω m ω → m ω := fun c =>
  run (fun a => pure a) c

def shift : [Monad m] → ((α → m ω) → ContT ω m ω) → ContT ω m α := fun f =>
  fun k => reset (f k)

def callCC : [Monad m] → ((α → ContT ω m β) → ContT ω m α) → ContT ω m α := fun f =>
  fun k => f (fun a => fun _ => k a) k
