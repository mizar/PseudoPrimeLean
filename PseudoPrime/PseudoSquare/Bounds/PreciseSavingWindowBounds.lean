/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Numerical certificates for the precise-saving winning window

The interval forty-four through forty-six is selected by the PseudoSquare public
candidate minimum. Its logarithm certificates are therefore kept in this comparison
leaf, separate from the cutoff-thirty-one LLS constant and root providers. Adjusting
the winning window does not change the actual-witness or cumulative radius foundation.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The logarithm of four lies in the rational interval needed by the winning window.
Input: none. Claim: the strict bounds 1.38 and 1.39.
Proof: use the existing certified logarithm of two.
Role: move between the input logarithm and the original quadratic level. -/
theorem precise_window_log_four : (138 / 100 : ℝ) < Real.log 4 ∧ Real.log 4 < (139 / 100 : ℝ) := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num only, Real.log_pow]
  norm_num only
  exact ⟨by linarith only [Real.log_two_gt_d9], by linarith only [Real.log_two_lt_d9]⟩

/-- The logarithm of 45.38 exceeds 3.8.
Input: none. Claim: a strict lower bound for the old radius's nested logarithm.
Proof: reflect a twenty-term rational Taylor interval.
Role: the lower edge of the complete old-minimum comparison. -/
private theorem precise_window_log_lower : (19 / 5 : ℝ) < Real.log (2269 / 50 : ℝ) := by
  have hc : Analysis.rationalLogIntervalCheck (2269 / 50) 6 20 (381 / 100) (191 / 50) = true := by
    decide +kernel
  have hb := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  exact (by norm_num only : (19 / 5 : ℝ) < 381 / 100).trans_le hb

/-- The logarithm of 47.39 is below 3.9.
Input: none. Claim: a strict upper bound for the new radius's nested logarithm.
Proof: reflect a twenty-term rational Taylor interval.
Role: certify the upper edge without sampling endpoints. -/
private theorem precise_window_log_upper : Real.log (4739 / 100 : ℝ) < (39 / 10 : ℝ) := by
  have hc : Analysis.rationalLogIntervalCheck (4739 / 100) 6 20 (77 / 20) (387 / 100) = true := by
    decide +kernel
  have hb := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  exact hb.trans_lt (by norm_num only : (387 / 100 : ℝ) < 39 / 10)

/-- The former additive-two elementary root exceeds sixty-five throughout the window.
Input: a logarithmic input at least forty-four. Claim: the old root's strict lower bound.
Proof: combine the original-level and nested-logarithm lower certificates.
Role: show that the retained cap 4093 beats the former elementary candidate. -/
theorem precise_window_refined_gt {L : ℝ} (hL : 44 ≤ L) :
    65 < L + Real.log 4 + (24 / 5 : ℝ) * Real.log (L + Real.log 4) + 2 := by
  have hq : (2269 / 50 : ℝ) < L + Real.log 4 := by linarith only [hL, precise_window_log_four.1]
  have hz :=
    precise_window_log_lower.trans_le
      (Real.log_le_log (by norm_num only : (0 : ℝ) < 2269 / 50) hq.le)
  linarith only [hq, hz]

/-- The retained-saving root lies strictly between nine and sixty-three on the full window.
Input: a logarithmic input between forty-four and forty-six.
Claim: both root signs and the strict upper comparison hold continuously.
Proof: monotonicity of logarithms and the two rational endpoint certificates.
Role: prove the new radius is below 3969 before comparing the complete old minimum. -/
theorem precise_window_prime31_bounds {L : ℝ} (hL : 44 ≤ L) (hU : L ≤ 46) :
    9 < (33 / 31 : ℝ) * (L + Real.log 4) + (4 / 5 : ℝ) * Real.log (L + Real.log 4) + 18327 / 2000 ∧
      (33 / 31 : ℝ) * (L + Real.log 4) + (4 / 5 : ℝ) * Real.log (L + Real.log 4) + 18327 / 2000 <
        63 := by
  have hlo : (2269 / 50 : ℝ) < L + Real.log 4 := by linarith only [hL, precise_window_log_four.1]
  have hhi : L + Real.log 4 < (4739 / 100 : ℝ) := by linarith only [hU, precise_window_log_four.2]
  have hzl :=
    precise_window_log_lower.trans_le
      (Real.log_le_log (by norm_num only : (0 : ℝ) < 2269 / 50) hlo.le)
  have hzu :=
    (Real.log_le_log ((by norm_num only : (0 : ℝ) < 2269 / 50).trans hlo) hhi.le).trans_lt
      precise_window_log_upper
  exact ⟨by linarith only [hlo, hzl], by linarith only [hhi, hzu]⟩

end PseudoPrime.PseudoSquare
