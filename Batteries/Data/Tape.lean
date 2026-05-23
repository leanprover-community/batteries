module

/-! # Tape data structure

The tape data structure mimics the structure of film reels and data cassettes,
not as physical media but as an abstract data type.

The model consists of two reels:

* The `leftReel` is the list of data before the head, in reverse order.
* The `rightReel` is the list of data after the head, in order.

The read/write head of the tape is at the interface of the two reels. Thus the
next value is the head of the `rightReel` and the latest value is the head of
the `leftReel`. The start position for the head is when the `leftReel` is empty
and the end position is when `rightReel` is empty.

The tape is capable of `rewind` and `forward` to move the tape head. It can
also `read`/`write` at the tape head. It also supports `copy`/`insert`/`delete`
editing features.
-/

set_option linter.missingDocs false in
/-- Tape data structure.

A tape consists of two reels:

* The `leftReel` is the list of data before the head, in reverse order.
* The `rightReel` is the list of data after the head, in order.

The read/write head of the tape is at the interface of the two reels. Thus the
next value is the head of the `rightReel` and the latest value is the head of
the `leftReel`. The start position for the head is when the `leftReel` is empty
and the end position is when `rightReel` is empty.
-/
@[ext]
public structure Batteries.Tape (α : Type _) where
  public leftReel : List α
  public rightReel : List α
attribute [inherit_doc Batteries.Tape] Batteries.Tape.leftReel Batteries.Tape.rightReel

/-- Convert a list to a tape. -/
@[inline]
public def List.toTape : List α → Batteries.Tape α := .mk []

namespace Batteries.Tape
open List (reverseAux)

/-- Convert a tape to a list. -/
@[inline]
public def toList (t : Tape α) : List α := reverseAux t.leftReel t.rightReel

/-- Get position of the tape head. -/
@[inline]
public def position (t : Tape α) : Nat := t.leftReel.length

/-- Get length of tape remaining from the tape head. -/
@[inline]
public def remaining (t : Tape α) : Nat := t.rightReel.length

/-- Total length of the tape. -/
public abbrev length (t : Tape α) : Nat := t.position + t.remaining

/-- Check whether position is at the end of tape. -/
@[inline]
public def endOfTape (t : Tape α) : Bool := t.rightReel.isEmpty

/-- Check whether position is at the start of tape. -/
@[inline]
public def startOfTape (t : Tape α) : Bool := t.leftReel.isEmpty

/-- Rewind to start of tape. -/
@[inline]
public def reset (t : Tape α) : Tape α := ⟨[], t.toList⟩

/-- Read the value at the current tape position, assuming not at the end of the tape. -/
@[inline]
public def read (t : Tape α) (h : ¬t.endOfTape) : α :=
  match t, h with | ⟨_, x :: _⟩, _ => x

/-- Read the value at the current tape position, or `none` if at end of tape. -/
@[inline]
public abbrev read? (t : Tape α) : Option α :=
  if h : t.endOfTape then none else t.read h

/-- Read the value at the current tape position. Panic if at end of tape. -/
public abbrev read! (t : Tape α) [Inhabited α] : α :=
  if h : t.endOfTape then panic! "empty tape" else t.read h

/-- Write a value at the tape head and advance the head.

If the head is at the end of the tape then the tape will be extended.
-/
@[inline]
public def write (t : Tape α) (x : α) : Tape α := ⟨x :: t.leftReel, t.rightReel.tail⟩

/-- Copy up to `n` values from the tape position.

If `n > t.remaining` then only the remaining values up to the end will be returned.
-/
@[inline]
public def copy (t : Tape α) (n : Nat) : List α := t.rightReel.take n

/-- Delete up to `n` values from the tape position.

If `n > t.remaining` then the tape will be deleted to the end.
-/
@[inline]
public def delete (t : Tape α) (n : Nat) : Tape α := ⟨t.leftReel, t.rightReel.drop n⟩

/-- Insert a list of values at the current tape position and advance the head. -/
@[inline]
public def insert (t : Tape α) (l : List α) : Tape α := ⟨reverseAux l t.leftReel, t.rightReel⟩


/-- Forward the tape up to `n` steps.

If `n ≤ t.remaining` then forward the tape to position `t.position + n`.
Otherwise, forward to the end of tape.
-/
@[inline]
public def forward : Tape α → Nat → Tape α
  | t@⟨_, []⟩, _ | t, 0 => t
  | ⟨l, x :: r⟩, n + 1 => forward ⟨x :: l, r⟩ n

/-- Rewind tape up to `n` steps.

If `n ≤ t.position` then rewind the tape to position `t.position - n`.
Otherwise, rewind to the start of tape.
-/
@[inline]
public def rewind : Tape α → Nat → Tape α
  | t@⟨[], _⟩, _ | t, 0 => t
  | ⟨x :: l, r⟩, n + 1 => rewind ⟨l, x :: r⟩ n

public instance : Std.Stream (Tape α) α where
  next?
  | ⟨_, []⟩ => none
  | ⟨l, x :: r⟩ => some (x, ⟨x :: l, r⟩)

public instance [Pure m] : Std.Iterator (Tape α) m α where
  IsPlausibleStep
    | ⟨⟨_, r⟩⟩, .done => r = []
    | _, .skip _ => False
    | ⟨⟨l, r⟩⟩, .yield ⟨⟨l', r'⟩⟩ x => l' = x :: l ∧ r = x :: r'
  step it := pure <| .deflate <| match it with
    | ⟨⟨_, []⟩⟩ =>  .done rfl
    | ⟨⟨l, x :: r⟩⟩ => .yield ⟨⟨x :: l, r⟩⟩ x ⟨rfl, rfl⟩

def finitenessRelation [Pure m] : Std.Iterators.FinitenessRelation (Tape α) m where
  Rel := InvImage WellFoundedRelation.rel (·.internalState.remaining)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h :=
    match it, it', h with
    | ⟨⟨_, _⟩⟩, ⟨⟨_, _⟩⟩, ⟨.yield ⟨⟨_, _⟩⟩ _, rfl, ⟨rfl, rfl⟩⟩ => Nat.lt_succ_self _

instance [Pure m] : Std.Iterators.Finite (Tape α) m :=
  .of_finitenessRelation finitenessRelation

instance [Pure m] [Monad n] : Std.IteratorLoop (Tape α) m n :=
  .defaultImplementation
