/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Default
import Data.Real.Basic
import Analysis.Calculus.ParametricIntegral
import Analysis.Calculus.ContDiff
import Analysis.SpecialFunctions.Trigonometric.Deriv


namespace Section17sheet3solutions

/-

# Smooth functions

-/
noncomputable def φ₁ : ℝ → ℝ × ℝ := fun x => (Real.cos x, Real.sin x)

example : ContDiffOn ℝ ⊤ φ₁ (Set.Icc 0 1) :=
  by
  apply ContDiffOn.prod
  · apply ContDiff.contDiffOn
    exact Real.contDiff_cos
  · apply ContDiff.contDiffOn
    exact Real.contDiff_sin

open Real

noncomputable def φ₂ : ℝ → ℝ × ℝ × ℝ := fun x => (Real.sin x, x ^ 4 + 37 * x ^ 2 + 1, abs x)

example : ContDiffOn ℝ ⊤ φ₂ (Set.Icc 0 1) :=
  contDiff_sin.ContDiffOn.Prod <|
    (((contDiff_id.pow 4).add (contDiff_const.mul (contDiff_id.pow 2))).add
            contDiff_const).ContDiffOn.Prod <|
      contDiffOn_id.congr fun x hx => abs_of_nonneg hx.1

/- Let `a≤b` and `c≤d` be reals. Let φ : [a,b] → [c,d] and ψ : [c,d] → [a,b]
  be inverse bijections, and assume φ is smooth and φ' is nonvanishing
  on [a,b]. Then ψ is smooth and ψ' is nonvanishing on [c,d],
  and ψ'(y)*φ'(ψ(y))=1.
-/
example (φ : ℝ → ℝ) (ψ : ℝ → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hφ : ∀ x, x ∈ Set.Icc a b → φ x ∈ Set.Icc c d) (hψ : ∀ y, y ∈ Set.Icc c d → ψ y ∈ Set.Icc a b)
    (left_inv : ∀ x, x ∈ Set.Icc a b → ψ (φ x) = x) (right_inv : ∀ y, y ∈ Set.Icc c d → φ (ψ y) = y)
    (hφdiff : ContDiffOn ℝ ⊤ φ (Set.Icc a b))
    (hφregular : ∀ x, x ∈ Set.Icc a b → fderiv ℝ φ x ≠ 0) :
    ContDiffOn ℝ ⊤ ψ (Set.Icc c d) ∧
      ∀ y, y ∈ Set.Icc c d → ∀ z, fderiv ℝ ψ y (fderiv ℝ φ (ψ y) z) = z :=
  sorry

/-
Heather Macbeth: @Kevin Buzzard This is a toy case of the inverse function theorem, 
but you might need to glue together several related results. Some starting points: 
docs#cont_diff_at.to_local_inverse, docs#has_strict_fderiv_at.local_inverse_unique

Heather Macbeth: If you want to construct the inverse, and you want to avoid invoking 
the inverse function theorem on Banach spaces, you can also route through order theory 
for a purely one-dimensional construction. Look at the construction of docs#real.arctan 
for a model; it uses docs#strict_mono_on.order_iso
-/
end Section17sheet3solutions

