/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalTheorem11S1Subgroup
public import PseudoPrime.Analysis.RetainedSavingPart1Separation
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants

/-! # Shared Part 1 root estimates and the reference retained-saving radius -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The Part 1 correction with constant 7031/5000, the exact prime-factor
loss and twice the reciprocal saving A*(q). Its nonnegative part defines
the new radius and is used by the generic root comparison below. -/
noncomputable def retainedSavingCorrectionTerm (q : ℕ) : ℝ :=
  max 0
    (2 * Real.log (Real.log q) + 7031 / 5000 +
        2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q -
      2 * refinedAuxiliaryTerm q)

/-- The new Part 1 radius root is log q plus the retained-saving correction.
Its square is the prime search cutoff. The definition is factorization-sensitive. -/
noncomputable def retainedSavingRadiusRoot (q : ℕ) : ℝ :=
  Real.log q + retainedSavingCorrectionTerm q

/-- At q ≥ 3000, any real root y ≥ log q satisfies the squared-log ratio
bound below. Apply the generic antitone ratio above eight. This gives the
common-factor loss for arbitrary admissible Part 1 radii. -/
theorem log_sq_root_le_level_ratio {q : ℕ} (hq : 3000 ≤ q) {y : ℝ} (hy : Real.log q ≤ y) :
    (Real.log (y ^ 2)) ^ 2 ≤ 4 * y * (Real.log (Real.log q)) ^ 2 / Real.log q := by
  have hL := Analysis.eight_lt_log_level hq
  have hy0 : 0 < y := by linarith only [hL, hy]
  have h := Analysis.strictAntiOn_logSquareRatio.antitoneOn hL.le (hL.le.trans hy) hy
  change (Real.log y) ^ 2 / y ≤ (Real.log (Real.log q)) ^ 2 / Real.log q at h
  have hh := (div_le_iff₀ hy0).mp h
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith only [hh]

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH and prime triviality through y² with y ≥ log q and q ≥ 3000,
the full-level weighted sum has the refined upper bound with A*(q).
Use the arbitrary-cutoff estimate and monotonicity of the saving before
multiplication. This upper interface does not fix the correction constant. -/
theorem characterLogWeightedSum_re_le_refined_root {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hq : 3000 ≤ q) (hN : 2 ≤ χ.conductor) (hne : χ.primitiveCharacter ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : Real.log q ≤ y)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ y ^ 2 → χ p = 1) :
    (characterLogWeightedSum (y ^ 2) χ).re ≤
      (2 * y + 2 + Real.log (y ^ 2)) * (Real.log q / 2 + 9 / 50 - refinedAuxiliaryTerm q) +
          (1 / 2 : ℝ) * (Real.log q - Real.log Real.pi) * Real.log (y ^ 2) -
        11 / 4 := by
  have hL := Analysis.eight_lt_log_level hq
  have hy0 : 0 < y := by linarith only [hL, hy]
  have hx : (64 : ℝ) ≤ y ^ 2 := by nlinarith only [hL, hy]
  have hs : Real.sqrt (y ^ 2) = y := Real.sqrt_sq hy0.le
  have h :=
    characterLogWeightedSum_re_le_refined_fullLevel χ hN hne hGRH hx hL
      (by
        rw [hs]; exact hy)
      htrivial
  rw [hs] at h
  have hlog : 2 * Real.log (Real.log q) ≤ Real.log (y ^ 2) := by
    rw [Real.log_pow]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith only [hL]) hy) (by norm_num only)
  have hA :
    refinedAuxiliaryTerm q ≤ max 0 (Real.log (y ^ 2) - 32873 / 20800 - primeFactorLogSum q) :=
    max_le_max (le_refl _) (by linarith only [hlog])
  have hc : 0 ≤ 2 * y + 2 + Real.log (y ^ 2) :=
    add_nonneg (add_nonneg (mul_nonneg (by norm_num only) hy0.le) (by norm_num only))
      (Real.log_nonneg (le_trans (by norm_num only) hx))
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_left hA (Real.log q / 2 + 9 / 50)) hc
  linarith only [h, hm]

end PseudoPrime.LLS
