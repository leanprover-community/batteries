import Batteries.Util.ProofWanted

/-!
# Tests for transparent (body-ful) `def_wanted`

A `def_wanted` *with a body* is **transparent**: emitted as a genuine `@[reducible]` definition
wrapped in `DerivedWanted`, with `❰foo❱` inlining it (projecting the carried value). This makes
`❰foo❱` definitionally equal to its body — so derived accessors over opaque holes compose — while
keeping the placeholder unusable as a direct inhabitant of its type and introducing no `axiom`/`sorry`.
A bodyless `def_wanted` stays an opaque `DefWanted` hole.
-/

namespace TransparentTests

universe u

/-- An opaque leaf hole (think: a bundled "functor"). -/
def_wanted F (k : Type u) : Type u → Type u

/-- A transparent derived declaration built from the hole. -/
def_wanted G (k : Type u) (x : Type u) : Type u := (❰F❱ k) x

/-! ## Definitional transparency

`❰G❱` βιδ-reduces to its body, so these `rfl`s type-check — the whole point of transparency. -/

theorem_wanted G_defeq (k x : Type u) : ❰G❱ k x = (❰F❱ k) x := rfl

/-! Transparency composes through the elaborator's machinery on the *concerning* shapes. -/

/-- implicit user argument, inferred through the inlined reference -/
def_wanted Gi {α : Type u} (_a : α) : Type u := (❰F❱ α) α
theorem_wanted Gi_defeq {α : Type u} (a : α) : ❰Gi❱ a = (❰F❱ α) α := rfl

/-- instance user argument: synthesised from context and threaded through the inlined lambda -/
class Cls (α : Type u) : Prop
def_wanted Gc (α : Type u) [Cls α] : Type u := (❰F❱ α) α
theorem_wanted Gc_defeq (α : Type u) [Cls α] : ❰Gc❱ α = (❰F❱ α) α := rfl

/-- transitive: transparent → transparent → hole inlines down to the leaf -/
def_wanted G2 (k x : Type u) : Type u := (❰G❱ k x)
theorem_wanted G2_defeq (k x : Type u) : ❰G2❱ k x = (❰F❱ k) x := rfl

/-! Referencing a *universe-polymorphic* transparent def at a *concrete* universe. The referenced
decl's level params must be rewritten to holes in the inlined binder types; otherwise the fixed
`Type` here clashes with the reference's `Type u` (regression: this used to fail "Type vs Type u"). -/

def_wanted Gconcrete : Type := (❰G❱ Nat Nat)
theorem_wanted Gconcrete_defeq : ❰Gconcrete❱ = (❰F❱ Nat) Nat := rfl

/-! ## The bundled-accessor pattern

A wanted *instance* whose payload mentions a transparent reference is well-formed (because the
reference is a real value), and is usable at the transparent value's unfolding. This is the shape
that makes a bundled `Functor`-valued hole usable as `GrpObj (Jacobian C)` downstream. -/

instance_wanted gInst (k x : Type u) : Inhabited (❰G❱ k x)
def_wanted gInst_use (k x : Type u) : Inhabited ((❰F❱ k) x) := ❰gInst❱ k x

/-! ## Obfuscation

A transparent `def_wanted` is a `DerivedWanted`-wrapped placeholder, not a usable value of its type:
it cannot be used directly, only via `❰…❱`. -/

/--
info: G : Type u_1 → Type u_1 → {d_F : (k : Type u_1) → (F k).Val} → DerivedWanted (Type u_1)
-/
#guard_msgs in #check @G

/--
error: Type mismatch
  G
has type
  Type → Type → {d_F : (k : Type) → (F k).Val} → DerivedWanted Type
but is expected to have type
  Type → Type
-/
#guard_msgs in example : Type → Type := G

/-! ## Soundness: no axioms

The transparent machinery is axiom-free — a transparent def is a real definition parametrised over
its opaque holes. -/

/--
info: '_private.BatteriesTest.def_wanted_transparent.0.TransparentTests.G_defeq' does not depend on any axioms
-/
#guard_msgs in #print axioms G_defeq

/--
info: '_private.BatteriesTest.def_wanted_transparent.0.TransparentTests.G2_defeq' does not depend on any axioms
-/
#guard_msgs in #print axioms G2_defeq

end TransparentTests
