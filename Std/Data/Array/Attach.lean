import Std.Data.List.Basic

namespace Array

/--
Unsafe implementation of `attach`, taking advantage of the fact that the representation of
`Array {x // x ∈ xs}` is the same as the input `Array α`.
-/
@[inline] private unsafe def attachImpl (xs : Array α) : Array {x // x ∈ xs} := unsafeCast xs

/-- "Attach" the proof that the elements of `xs` are in `xs` to produce a new list
  with the same elements but in the type `{x // x ∈ xs}`. -/
@[implemented_by attachImpl] def attach (xs : Array α) : Array {x // x ∈ xs} :=
  ⟨xs.data.pmap Subtype.mk fun _ => Array.Mem.mk⟩

end Array
