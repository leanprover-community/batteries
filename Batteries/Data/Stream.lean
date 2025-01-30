/-
Copyright (c) 2024 François G. Dorais. All rights reserved.
Released under Apache 2. license as described in the file LICENSE.
Authors: François G. Dorais
-/

namespace Stream

/-- Drop up to `n` values from the stream `s`. -/
def drop [Stream σ α] (s : σ) : Nat → σ
  | 0 => s
  | n+1 =>
    match next? s with
    | none => s
    | some (_, s) => drop s n

/-- Read up to `n` values from the stream `s` as a list from first to last. -/
def take [Stream σ α] (s : σ) : Nat → List α × σ
  | 0 => ([], s)
  | n+1 =>
    match next? s with
    | none => ([], s)
    | some (a, s) =>
      match take s n with
      | (as, s) => (a :: as, s)

@[simp] theorem fst_take_zero [Stream σ α] (s : σ) :
    (take s 0).fst = [] := rfl

theorem fst_take_succ [Stream σ α] (s : σ) :
    (take s (n+1)).fst = match next? s with
      | none => []
      | some (a, s) => a :: (take s n).fst := by
  simp only [take]; split <;> rfl

@[simp] theorem snd_take_eq_drop [Stream σ α] (s : σ) (n : Nat) :
    (take s n).snd = drop s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [take, drop]
    split <;> simp [ih]

/-- Tail recursive version of `Stream.take`. -/
def takeTR [Stream σ α] (s : σ) (n : Nat) : List α × σ :=
  loop s [] n
where
  /-- Inner loop for `Stream.takeTR`. -/
  loop (s : σ) (acc : List α)
    | 0 => (acc.reverse, s)
    | n+1 => match next? s with
      | none => (acc.reverse, s)
      | some (a, s) => loop s (a :: acc) n

theorem fst_takeTR_loop [Stream σ α] (s : σ) (acc : List α) (n : Nat) :
    (takeTR.loop s acc n).fst = acc.reverseAux (take s n).fst := by
  induction n generalizing acc s with
  | zero => rfl
  | succ n ih => simp only [take, takeTR.loop]; split; rfl; simp [ih]

theorem fst_takeTR [Stream σ α] (s : σ) (n : Nat) : (takeTR s n).fst = (take s n).fst :=
  fst_takeTR_loop ..

theorem snd_takeTR_loop [Stream σ α] (s : σ) (acc : List α) (n : Nat) :
    (takeTR.loop s acc n).snd = drop s n := by
  induction n generalizing acc s with
  | zero => rfl
  | succ n ih => simp only [takeTR.loop, drop]; split; rfl; simp [ih]

theorem snd_takeTR [Stream σ α] (s : σ) (n : Nat) :
    (takeTR s n).snd = drop s n := snd_takeTR_loop ..

@[csimp] theorem take_eq_takeTR : @take = @takeTR := by
  funext; ext : 1; rw [fst_takeTR]; rw [snd_takeTR, snd_take_eq_drop]

end Stream

@[simp] theorem List.stream_drop_eq_drop (l : List α) : Stream.drop l n = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    match l with
    | [] => rfl
    | _::_ => simp [Stream.drop, List.drop_succ_cons, ih]

@[simp] theorem List.stream_take_eq_take_drop (l : List α) :
    Stream.take l n = (l.take n, l.drop n) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    match l with
    | [] => rfl
    | _::_ => simp [Stream.take, ih]
