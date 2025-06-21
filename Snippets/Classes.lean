


class Traversable (t : Type _ → Type _) extends Functor t where
  traverse : [Applicative f] → (α → f β) → t α → f (t β)


def List.traverse : [Applicative f] → (α → f β) → List α → f (List β) :=
  fun f xs => xs.foldr (fun x acc => (·  :: ·) <$> f x <*> acc ) (pure [])

instance : Applicative List where
  pure x := [x]
  seq xs  ys := xs.flatMap (fun f => ys () |>.map f)

instance : Traversable List where
  traverse f xs := List.traverse f xs
