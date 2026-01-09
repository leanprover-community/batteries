/-
Copyright (c) 2026 Owen Shepherd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen Shepherd
-/
module

namespace Alternative

private partial def many.aux [Alternative f] [Nonempty (f (List α))]
    (p : f α) : f (List α) :=
  List.cons <$> p <*> many.aux p <|> pure []

/--
Zero or more Alternatives.
For example, given a Parser, which implements Alternative, you can use the `many` combinator
to parse zero or more items.
-/
partial def many [Alternative f]
    (p : f α) : f (List α) :=
  letI : Nonempty (f (List α)) := ⟨pure []⟩
  List.cons <$> p <*> many.aux p <|> pure []

/--
One or more Alternatives.
For example, given a Parser, which implements Alternative, you can use the `many1` combinator
to parse one or more items.
-/
def many1 [Alternative f] [Inhabited (f (List α))]
    (p : f α) : f (Σ n, Vector α (1 + n)) :=
  let g x xs := ⟨xs.1, Vector.singleton x ++ xs.2⟩
  let toVec (l : List α) : Σ n, Vector α n :=
    let arr := List.toArray l
    ⟨arr.size, ⟨arr, rfl⟩⟩
  let manyVec : f (Σ n, (Vector α n)) := toVec <$> Alternative.many p
  g <$> p <*> manyVec <|> Alternative.failure
