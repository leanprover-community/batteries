/-
Copyright (c) 2025 Owen Shepherd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen Shepherd
-/

/--
Zero or more Alternatives.
For example, given a Parser, which implements Alternative, you can use the `many` combinator
to parse zero or more items.
-/
partial def Alternative.many {a : Type} [Alternative f] [Inhabited (f (List a))]
    (p : f a) : f (List a) :=
  List.cons <$> p <*> Alternative.many p <|> pure []

/--
One or more Alternatives.
For example, given a Parser, which implements Alternative, you can use the `many1` combinator
to parse one or more items.
-/
def Alternative.many1 [Alternative f] [Inhabited (f (List a))]
    (p : f a) : f (Σ n, Vector a (1 + n)) :=
  let g x xs := ⟨xs.1, Vector.singleton x ++ xs.2⟩
  let toVec (l : List a) : Σ n, Vector a n :=
    let arr := List.toArray l
    ⟨arr.size, ⟨arr, rfl⟩⟩
  let manyVec : f (Σ n, (Vector a n)) := toVec <$> Alternative.many p
  g <$> p <*> manyVec <|> Alternative.failure
