/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import Paperproof


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro p
  left
  exact p
  done

example : Q → P ∨ Q := by
  intro q
  right
  exact q
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro pq
  intro pr
  intro qr
  cases' pq with p q
  . apply pr
    exact p
  . apply qr
    exact q
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro pq
  cases' pq with p q
  . right
    exact p
  . left
    exact q
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  . intro pqr
    cases' pqr with pq r
    . cases' pq with p q
      . left; exact p
      . right; left; exact q
    . right; right; exact r
  . intro pqr
    cases' pqr with p qr
    . left; left; exact p
    . cases' qr with q r
      . left; right; exact q
      . right; exact r
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro pr qs pq
  cases' pq with p q
  . apply pr at p
    left
    exact p
  . apply qs at q
    right
    exact q
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro pq
  intro pr
  cases' pr with p r
  . apply pq at p
    left
    exact p
  . right
    exact r
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro pr qs
  constructor
  . intro pq
    rw [pr] at pq
    rw [qs] at pq
    exact pq
  . intro rs
    rw [← pr] at rs
    rw [← qs] at rs
    exact rs
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  . intro npq
    constructor
    . intro p
      apply npq
      left
      exact p
    . intro q
      apply npq
      right
      exact q
  . intro npnq
    intro pq
    cases' npnq with np nq
    cases' pq with p q
    . apply np
      exact p
    . apply nq
      exact q
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  . intro npq
    by_cases p: P
    . right
      intro q
      apply npq
      constructor
      . exact p
      . exact q
    . left
      exact p
  . intro npnq
    . intro pq
      cases' pq with p q
      cases' npnq with np np
      . apply np
        exact p
      . apply np
        exact q
  done
