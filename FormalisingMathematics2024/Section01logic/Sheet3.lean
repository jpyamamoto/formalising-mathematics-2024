/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro t
  change True → False at t
  apply t
  triv
  done

example : False → ¬True := by
  intro f
  change True → False
  intro t
  exact f
  done

example : ¬False → True := by
  intro nf
  change False → False at nf
  by_contra nt
  change True → False at nt
  apply nt
  triv
  done

example : True → ¬False := by
  intro t
  change False → False
  intro f
  exact f
  done

example : False → ¬P := by
  intro f
  change P → False
  intro p
  exact f
  done

example : P → ¬P → False := by
  intro p
  intro np
  change P → False at np
  apply np
  exact p
  done

example : P → ¬¬P := by
  intro p
  intro np
  apply np
  exact p
  done

example : (P → Q) → ¬Q → ¬P := by
  intro pq
  intro nq
  intro p
  by_cases hp : P
  apply pq at hp
  apply nq
  exact hp
  apply hp
  exact p
  done

example : ¬¬False → False := by
  intro nnf
  apply nnf
  intro f
  exact f
  done

example : ¬¬P → P := by
  intro nnp
  by_cases np: P
  exact np
  apply nnp at np
  exfalso
  exact np
  done

example : (¬Q → ¬P) → P → Q := by
  intro nqnp
  intro p
  by_cases hq: Q
  exact hq
  by_contra nq
  apply nqnp at nq
  apply nq
  exact p
  done
