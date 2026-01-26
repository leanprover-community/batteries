/-
Copyright (c) 2026 Owen Shepherd. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen Shepherd
-/
module

public section

namespace Alternative

/--
Zero or more Alternatives.
For example, given a Parser, which implements Alternative, you can use the `many` combinator
to parse zero or more items.
-/
partial def many [Alternative f]
    (p : f α) : f (List α) :=
  List.cons <$> p <*> many p <|> pure []

/--
One or more Alternatives.
For example, given a Parser, which implements Alternative, you can use the `many1` combinator
to parse one or more items.
-/
def many1 [Alternative f] (p : f α) : f (List α) :=
  List.cons <$> p <*> many p
