/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet5 -- import a bunch of previous stuff

namespace Section2sheet6

open Section2sheet3solutions Section2sheet5solutions

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
  rw [tendsTo_def] at *
  intro ε hε
  specialize h (ε / 37)
  have h1: 0 < ε / 37 := by linarith
  apply h at h1
  cases' h1 with B hb
  use B
  intro n hbn
  specialize hb n hbn
  rw [← mul_sub]
  rw [abs_mul]
  rw [abs_of_nonneg] <;> linarith

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rw [tendsTo_def] at *
  intro ε hε
  specialize h (ε / c)
  have h1 : 0 < ε / c := by exact div_pos hε hc
  apply h at h1
  cases' h1 with B hb
  use B
  intro n hbn
  specialize hb n hbn
  rw [← mul_sub]
  rw [abs_mul]
  rw [abs_of_nonneg]
  rw [← lt_div_iff' hc]
  exact hb
  exact le_of_lt hc

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rw [tendsTo_def] at *
  intro ε hε
  specialize h (-(ε / c))
  have h1 : 0 < (-(ε / c)) := by
    rw [lt_neg]
    rw [SubtractionMonoid.toSubNegZeroMonoid.proof_1]
    rw [div_neg_iff]
    left
    constructor
    exact hε
    exact hc
  apply h at h1
  cases' h1 with B hb
  use B
  intro n hbn
  specialize hb n hbn
  rw [← mul_sub]
  rw [abs_mul]
  rw [abs_of_neg hc]
  rw [← lt_div_iff']
  rw [div_neg_eq_neg_div]
  exact hb
  linarith

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  have ht : c < 0 ∨ c = 0 ∨ c > 0 := by exact lt_trichotomy c 0
  cases' ht with lt get
  . exact tendsTo_neg_const_mul h lt
  . cases' get with eq gt
    . rw [eq]
      simp
      exact tendsTo_const 0
    . exact tendsTo_pos_const_mul h gt

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
  simpa [mul_comm] using tendsTo_const_mul c h

-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by
  simpa using tendsTo_add h1 h2

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  constructor
  . intro h
    have h1 := tendsTo_sub h (tendsTo_const t)
    simp at h1
    exact h1
  . intro h
    simpa using tendsTo_add h (tendsTo_const t)

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  intro ε hε
  obtain ⟨B1, hb1⟩ := ha ε hε
  obtain ⟨B2, hb2⟩ := hb 1 zero_lt_one
  use max B1 B2
  intro n hn
  specialize hb1 n (le_of_max_le_left hn)
  specialize hb2 n (le_of_max_le_right hn)
  simp at *
  rw [abs_mul]
  rw [← mul_one (|a n|)] at hb1
  exact mul_lt_of_mul_lt_of_nonneg_left hb1 (le_of_lt hb2) (abs_nonneg (a n))

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
sorry

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  sorry

end Section2sheet6
