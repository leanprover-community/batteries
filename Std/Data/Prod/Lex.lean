/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

namespace Prod.Lex

instance [αeqDec : DecidableEq α] {r : α → α → Prop} [rDec : DecidableRel r]
    {s : β → β → Prop} [sDec : DecidableRel s] : DecidableRel (Prod.Lex r s)
  | (a, b), (a', b') =>
    match rDec a a' with
    | isTrue raa' => isTrue $ left b b' raa'
    | isFalse nraa' =>
      match αeqDec a a' with
      | isTrue eq => by
        subst eq
        cases sDec b b' with
        | isTrue sbb' => exact isTrue $ right a sbb'
        | isFalse nsbb' =>
          apply isFalse; intro contra; cases contra <;> contradiction
      | isFalse neqaa' => by
        apply isFalse; intro contra; cases contra <;> contradiction
