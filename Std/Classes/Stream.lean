import Std.WF
import Std.Data.Nat.Lemmas

class StreamAcc [Stream σ α] (s : σ) : Prop where
  acc : Acc (fun s' s : σ => ∃ a, Stream.next? s = some (a, s')) s

abbrev WellFoundedStream (σ : Type _) [Stream σ α] := ∀ s : σ, StreamAcc s

local instance [Stream σ α] : WellFoundedRelation {s : σ // StreamAcc s} :=
  .ofAcc fun s => ⟨s.1, s.2.1⟩

def StreamAcc.ofAcc [Stream σ α] {s : σ} (acc : Acc r s)
    (H : ∀ s a s', Stream.next? (s : σ) = some (a, s') → r s' s) :
    StreamAcc s :=
  ⟨Subrelation.accessible (fun ⟨_, h⟩ => H _ _ _ h) acc⟩

def StreamAcc.ofWF [Stream σ α] (wf : WellFoundedRelation σ)
    (H : ∀ s a s', Stream.next? (s : σ) = some (a, s') → wf.rel s' s) :
    WellFoundedStream σ :=
  fun s => StreamAcc.ofAcc (wf.wf.apply s) H

def StreamAcc.ofWFRestrict [Stream σ α] (p : σ → Prop) (wf : WellFoundedRelation σ)
    (H : ∀ s a s', p s → Stream.next? (s : σ) = some (a, s') → p s' ∧ wf.rel s' s)
    (hp : p s) : StreamAcc s :=
  ⟨Subrelation.accessible (fun ⟨_, h⟩ hy => H _ _ _ hy h) (.restriction p (wf.wf.apply s) hp)⟩

class FromStream (m : Type _ → Type _) (s : σ) (α : outParam (Type _)) where
  fromStream : (β → α → m β) → β → m β

@[specialize] partial def Stream.fromStream [Monad m] [Stream σ α]
    (s : σ) (f : β → α → m β) (b : β) : m β :=
  match Stream.next? s with
  | none => pure b
  | some (a, s') => f b a >>= Stream.fromStream s' f

instance (priority := low) [Monad m] (s : σ) [Stream σ α] : FromStream m s α where
  fromStream := Stream.fromStream s

@[specialize] def Stream.fromStreamWF [Monad m] [Stream σ α] (s : {s : σ // StreamAcc s})
    (f : β → α → m β) (b : β) : m β :=
  match h : Stream.next? s.1 with
  | none => pure b
  | some (a, s') =>
    have := ⟨_, h⟩
    f b a >>= Stream.fromStreamWF ⟨s', ⟨.inv s.2.1 this⟩⟩ f
termination_by _ s _ _ => s

instance (priority := low+1) [Monad m] [Stream σ α]
    (s : σ) [acc : StreamAcc s] : FromStream m s α where
  fromStream := Stream.fromStreamWF ⟨s, acc⟩

protected def Stream.forInWF [Stream σ α] [Monad m]
    (s : {s : σ // StreamAcc s}) (b : β) (f : α → β → m (ForInStep β)) : m β := do
  match h : Stream.next? s.1 with
  | some (a, s') => match (← f a b) with
    | ForInStep.done b  => return b
    | ForInStep.yield b =>
      have := ⟨_, h⟩
      Stream.forInWF ⟨s', ⟨.inv s.2.1 this⟩⟩ b f
  | none => return b
termination_by _ s _ _ => s

instance (priority := low+1)
    [ToStream ρ σ] [Stream σ α] [acc : WellFoundedStream σ] : ForIn m ρ α where
  forIn s b f := Stream.forInWF ⟨toStream s, acc _⟩ b f

structure StreamAccType (a : α)
def streamAcc := @StreamAccType.mk

instance [Stream σ α] (s : σ) [acc : StreamAcc s] : ForIn m (StreamAccType s) α where
  forIn _ b f := Stream.forInWF ⟨s, acc⟩ b f

def Array.collect (s : ρ) [ToStream ρ σ] [FromStream Id (toStream s) α] : Array α :=
  Id.run <| FromStream.fromStream (toStream s) (fun arr a => arr.push a) #[]

def Array.collect' [ForIn Id ρ α] (s : ρ) : Array α :=
  Id.run <| forIn s #[] fun a arr => .yield (arr.push a)

instance : WellFoundedStream (List α) :=
  .ofWF (measure List.length) fun
    | _::_, _, _, rfl => Nat.lt_succ_self _

instance : StreamAcc [a:b:c+1] := by
  refine StreamAcc.ofWFRestrict (·.step = c+1) (measure (fun a => a.2 - a.1))
    (fun | ⟨a, b, c₁⟩, n, ⟨a', b', c'⟩, e => ?_) rfl
  cases e; simp [Stream.next?]; split <;> intro h <;> cases h
  next ab => exact ⟨rfl, Nat.sub_lt_sub_left ab (Nat.lt_add_of_pos_right (Nat.succ_pos _))⟩

instance : StreamAcc (toStream [a:b:c+1]) := inferInstanceAs (StreamAcc [a:b:c+1])

#eval Array.collect [1:10:2] -- #[1, 3, 5, 7, 9]
#eval Array.collect #[1, 2] -- #[1, 2]
#reduce Array.collect [1:10:3] -- { data := [1, 4, 7] }
#reduce Array.collect [1:10:0] -- stuck
#reduce Array.collect [1, 2] -- { data := [1, 2] }

#eval Array.collect' [1:10:2] -- #[1, 3, 5, 7, 9]
#eval Array.collect' #[1, 2] -- #[1, 2]
#reduce Array.collect' [1:10:3] -- { data := [1, 4, 7] }
#reduce Array.collect' [1:10:0] -- { data := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] }
#reduce Array.collect' [1, 2] -- { data := [1, 2] }
