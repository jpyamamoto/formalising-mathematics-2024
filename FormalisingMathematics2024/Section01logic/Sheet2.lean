/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 2 : `true` and `false`

We learn about the `true` and `false` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones. Check out their explanations
in the course book. Or just try them out and hover over them to see
if you can understand what's going on.

* `triv`
* `exfalso`

-/


-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : True := by
  triv
  done

example : True → True := by
  intro t
  triv
  done

example : False → True := by
  intro f
  triv
  done

example : False → False := by
  intro f
  exact f
  done

example : (True → False) → False := by
  intro h
  apply h
  triv
  done

example : False → P := by
  intro f
  exfalso
  exact f
  done

example : True → False → True → False → True → False := by
  intro t1
  intro f1
  intro t2
  intro f2
  intro t3
  exact f1
  done

example : P → (P → False) → False := by
  intro p
  intro h
  apply h
  exact p
  done

example : (P → False) → P → Q := by
  intro h
  intro p
  exfalso
  apply h
  exact p
  done

example : (True → False) → P := by
  intro h
  exfalso
  apply h
  triv
  done
