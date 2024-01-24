/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro pq
  rw [pq]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro pq
  rw [pq]
  intro qp
  rw [qp]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro pq
  intro qr
  rw [pq]
  rw [← qr]
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro pq
  cases' pq with p q
  constructor
  exact q
  exact p
  intro qp
  cases' qp with q p
  constructor
  exact p
  exact q
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro pqr
  cases' pqr with pq r
  cases' pq with p q
  constructor
  exact p
  constructor
  exact q
  exact r
  intro pqr
  cases' pqr with p qr
  cases' qr with q r
  constructor
  constructor
  exact p
  exact q
  exact r
  done

example : P ↔ P ∧ True := by
  constructor
  intro p
  constructor
  exact p
  triv
  intro pt
  cases' pt with p t
  exact p
  done

example : False ↔ P ∧ False := by
  constructor
  intro f
  constructor
  exfalso
  exact f
  exact f
  intro pf
  cases' pf with p f
  exact f
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro pq
  intro rs
  constructor
  intro pr
  rw [pq] at pr
  rw [rs] at pr
  exact pr
  intro qs
  rw [← pq] at qs
  rw [← rs] at qs
  exact qs
  done

example : ¬(P ↔ ¬P) := by
  by_cases p : P
  intro pnp
  cases' pnp with h1 h2
  apply h1
  exact p
  exact p
  intro pnp
  cases' pnp with h1 h2
  apply h1
  apply h2
  exact p
  apply h2
  exact p
  done
