module

@[expose] public section

/-- Well-formedness relation for Bool.lt -/
instance Bool.lt_wfRel : WellFoundedRelation Bool where
  rel := (· < ·)
  wf := by
    apply WellFounded.intro
    intro b
    cases b with
    | false =>
      apply Acc.intro false
      intro y h
      cases y <;> contradiction
    | true =>
      apply Acc.intro true
      intro y h
      cases y with
      | false =>
        apply Acc.intro false
        intro z h'
        cases z <;> contradiction
      | true =>
        contradiction

/-- Well-formedness for Bool.gt -/
instance Bool.gt_wfRel : WellFoundedRelation Bool where
  rel := (· > ·)
  wf := by
    apply WellFounded.intro
    intro b
    cases b with
    | true =>
      apply Acc.intro true
      intro y h
      cases y <;> contradiction
    | false =>
      apply Acc.intro false
      intro y h
      cases y with
      | true =>
        apply Acc.intro true
        intro z h'
        cases z <;> contradiction
      | false =>
        contradiction
