/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel656

/-! # Common principal kernel for K137 and K197 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The main kernel for K137 and K197 has pole parameter 11/10 and
support ending at exp(21/8). Both comparisons use the same Mellin kernel. -/
noncomputable def gaussianKernel137 : LLS.PaperStatements.MellinKernel :=
  quarterKernel656

/-- At positive inputs the common main kernel is the explicit rational-pole profile. -/
theorem gaussianKernel137_transform {u : ℝ} (hu : 0 < u) :
    (gaussianKernel137.transform u).re = Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) u := by
  rw [gaussianKernel137, quarterKernel656, LLS.PaperStatements.rationalPole_transform _ _ _ _ hu,
    Complex.ofReal_re]

/-- The common kernel vanishes past the upper support boundary, so its principal
sum at cutoff X only needs arguments at most X times exp(21/8). -/
theorem gaussianKernel137_support {u : ℝ} (hu : Real.exp (21 / 8) < u) :
    (gaussianKernel137.transform u).re = 0 := by
  rw [gaussianKernel137_transform ((Real.exp_pos _).trans hu)]
  apply Analysis.rationalPoleProfile_eq_zero
  norm_num only at hu ⊢
  exact hu

/-- The character summand vanishes when its index lies beyond the scaled support.
This bound applies to the principal and all twisted finite sums. -/
theorem gaussianKernel137_summand_zero {q n : ℕ} (χ : DirichletCharacter ℂ q) {X : ℝ} (hX : 0 < X)
    (hn : X * Real.exp (21 / 8) < n) : gaussianKernel137.summand χ X n = 0 := by
  have hu : Real.exp (21 / 8) < (n : ℝ) / X :=
    (lt_div_iff₀ hX).2 (by simpa only [mul_comm] using hn)
  have hz :=
    Analysis.rationalPoleProfile_eq_zero 3 (5 / 11) (21 / 16)
      (by
        convert hu using 1
        norm_num only)
  rw [LLS.PaperStatements.MellinKernel.summand, gaussianKernel137, quarterKernel656,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ ((Real.exp_pos _).trans hu), hz,
    Complex.ofReal_zero, mul_zero, ite_self]

/-- The arithmetic side for the common kernel is a finite sum through its
scaled support endpoint. The zero term is retained in the finite range. -/
theorem gaussianKernel137_sum {q : ℕ} (χ : DirichletCharacter ℂ q) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℕ, gaussianKernel137.summand χ X n) =
      ∑ n ∈ Finset.range (⌊X * Real.exp (21 / 8)⌋₊ + 1), gaussianKernel137.summand χ X n := by
  apply tsum_eq_sum
  intro n hn
  apply gaussianKernel137_summand_zero χ hX
  exact
    (Nat.floor_lt (mul_nonneg hX.le (Real.exp_pos _).le)).1
      (Nat.lt_of_succ_le (Nat.le_of_not_lt (fun h ↦ hn (Finset.mem_range.mpr h))))

/-- The principal contribution for the K137/K197 kernel has the same
positive coefficient as the quarter-square kernel, at any later cutoff. -/
theorem gaussian_principal_delta_137 :
    71780481 / 100000000 <
      4 * (∫ u : ℝ in (0 : ℝ)..1, (gaussianKernel137.transform u).re / Real.sqrt u) -
        (gaussianKernel137.function (1 / 2)).re := by
  exact quarter_principal_delta_656

/-- The upper side of the K137/K197 principal coefficient enclosure,
using lower Taylor bounds for both positive exponentials. -/
theorem gaussian_principal_delta_upper :
    4 * (∫ u : ℝ in (0 : ℝ)..1, (gaussianKernel137.transform u).re / Real.sqrt u) -
        (gaussianKernel137.function (1 / 2)).re ≤
      0.71780482 := by
  rw [gaussianKernel137, quarterKernel656, LLS.PaperStatements.rationalPole_half_value,
    LLS.PaperStatements.rationalPole_cutoff_moment _ _ _ _ (by norm_num only)]
  norm_num only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.choose_zero_right, Nat.choose_self, Nat.choose_one_right, Nat.choose,
    Nat.factorial, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  have ha := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 231 / 80) 25
  have hb := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 21 / 16) 21
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ha hb
  have hi := one_div_le_one_div_of_le (by norm_num only) ha
  rw [one_div (Real.exp _), ← Real.exp_neg] at hi
  linarith only [hi, hb]

/-- For a positive integer in the support at scale X, the K137/K197
principal coefficient is the physical weight times the Mangoldt function. -/
theorem gaussian_principal_summand_137 {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : 0 < n)
    (hs : Real.log ((n : ℝ) / X) ≤ 21 / 8) :
    (gaussianKernel137.summand (1 : DirichletCharacter ℂ 1) X n).re =
      quarterWeight656 X n * ArithmeticFunction.vonMangoldt n := by
  exact quarter_summand_656 hX hn hs

end PseudoPrime.PrimeTestBounds.MillerRabin
