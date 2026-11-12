/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Real.Pi.Bounds

/-! # A rational certificate for the Lee–Nosal envelope -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For positive `x`, bounds `l ≤ log x ≤ u` and `log u ≤ v ≤ l`, together with
`pi ≤ P` and the displayed squared inequality, certify the lower bound `c` for the
Lee–Nosal error envelope. This separates rational endpoint checks from real logarithms. -/
theorem lee_nosal_envelope_of_sq {x l u v P c : ℝ} (hx : 0 < x) (hc : 0 ≤ c) (hlpos : 0 < l)
    (hvl : v ≤ l) (hl : l ≤ Real.log x) (hu : Real.log x ≤ u) (huv : Real.log u ≤ v)
    (hP : Real.pi ≤ P) (hsq : (8 * P * c) ^ 2 ≤ x * l ^ 2 * (l - v) ^ 2) :
    c ≤ Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  have hlogpos : 0 < Real.log x := hlpos.trans_le hl
  have hll := Real.log_le_log hlogpos hu
  have hgap : l - v ≤ Real.log x - Real.log (Real.log x) := by linarith only [hl, hll, huv]
  have hmul := mul_le_mul hl hgap (sub_nonneg.mpr hvl) hlogpos.le
  have hroot := Real.sqrt_nonneg x
  have hP0 : 0 ≤ P := le_trans Real.pi_pos.le hP
  have hleft : 0 ≤ 8 * P * c := mul_nonneg (mul_nonneg (by norm_num only) hP0) hc
  have hright : 0 ≤ Real.sqrt x * (l * (l - v)) :=
    mul_nonneg hroot (mul_nonneg hlpos.le (sub_nonneg.mpr hvl))
  have hsq' : (8 * P * c) ^ 2 ≤ (Real.sqrt x * (l * (l - v))) ^ 2 := by
    calc
      _ ≤ x * l ^ 2 * (l - v) ^ 2 := hsq
      _ = (Real.sqrt x * (l * (l - v))) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hx.le]
        ring
  have hrootbound : 8 * P * c ≤ Real.sqrt x * (l * (l - v)) := by
    nlinarith only [hsq', hleft, hright]
  have hmain := mul_le_mul_of_nonneg_left hmul hroot
  have hcmp := mul_nonneg (sub_nonneg.mpr hP) hc
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 8 * Real.pi)).2
  nlinarith only [hrootbound, hmain, hcmp]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
