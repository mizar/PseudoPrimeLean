/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialFixedPointConversions
public import PseudoPrime.Analysis.ExponentialFixedPointExecution

/-! # Exponential upper certificate for the first Gamma pole -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Kernel reduction checks the 64-step fixed-point certificate.
/-- An independent fixed-point certificate bounds the reciprocal
exponential needed at the left endpoint. -/
theorem quarter_gamma_exp_upper_check :
    1880000000000 ≤ Analysis.expFixedPointSignedLowerFast 377 50 1000000000 64 := by decide +kernel

/-- At the left endpoint, the exponential tail factor is at most `54/100000`.
The reciprocal of the certified positive exponential gives this bound. -/
theorem quarter_gamma_exp_upper : Real.exp (-(377 / 50 : ℝ)) ≤ 54 / 100000 := by
  have hcheck := quarter_gamma_exp_upper_check
  rw [Analysis.expFixedPointSignedLowerFast_eq] at hcheck
  have hp : 0 < Analysis.expFixedPointSignedLower 377 50 1000000000 64 :=
    lt_of_lt_of_le (by norm_num only) hcheck
  have h :=
    Analysis.exp_upper_of_signed_fixed_lower (-377) 50 1000000000 64 (by norm_num only)
      (by norm_num only) (by norm_num only) (by simpa only [neg_neg] using hp)
  have hc : (1880000000000 : ℝ) ≤ (Analysis.expFixedPointSignedLower 377 50 1000000000 64 : ℝ) := by
    exact_mod_cast hcheck
  norm_num only at h ⊢
  have hpos : 0 < (Analysis.expFixedPointSignedLower 377 50 1000000000 64 : ℝ) := by
    exact_mod_cast hp
  apply h.trans
  apply (div_le_iff₀ hpos).2
  nlinarith only [hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
