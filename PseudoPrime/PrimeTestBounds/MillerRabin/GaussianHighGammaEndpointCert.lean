/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaTail
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaRationalCert

/-! # Exact cutoff tests for the high Gaussian gamma moments -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The K186 decaying moment is
nonnegative at the certified cutoff 65. -/
theorem k186_gamma_decay_endpoint :
    0 ≤
      ∫ t in (0 : ℝ)..(65 : ℚ),
        HighGaussianKernel.k186.realProfile.eval t * Real.exp (-(((9 / 4 : ℚ) : ℝ)) * t) := by
  apply high_gamma_endpoint_nonneg .k186 (by norm_num only) (by norm_num only)
  exact k186_gamma_endpoint_check

/-- At 80, the K196 decaying moment has a deficit at most 806. -/
theorem k196_gamma_decay_deficit :
    max
        (-(∫ t in (0 : ℝ)..(80 : ℚ),
            HighGaussianKernel.k196.realProfile.eval t * Real.exp (-((11 / 4 : ℚ) : ℝ) * t)))
        0 ≤
      (806 : ℚ) := by
  apply high_gamma_endpoint_deficit .k196 (by norm_num only) (by norm_num only) (by norm_num only)
  exact k196_gamma_endpoint_check

/-- The K196 decay deficit is at most 806 throughout the certified tail. -/
theorem k196_gamma_decay_tail {z : ℝ} (hz : 80 ≤ z) :
    max
        (-(∫ t in (0 : ℝ)..z,
            HighGaussianKernel.k196.realProfile.eval t * Real.exp (-(11 / 4 : ℝ) * t)))
        0 ≤
      806 := by
  have hz' : (profileCorrectionEnd .k196 : ℝ) ≤ z := hz
  have h := (high_gamma_tail_deficits .k196 (s := 0) (d := 11 / 4) hz').2
  refine h.trans ?_
  simpa only [profileCorrectionEnd, Rat.cast_ofNat, Rat.cast_div, Int.cast_ofNat, Int.cast_natCast,
    Nat.cast_ofNat] using k196_gamma_decay_deficit

/-- For K186 the decaying gamma moment stays nonnegative past 65. -/
theorem k186_gamma_decay_tail {z : ℝ} (hz : 65 ≤ z) :
    0 ≤
      ∫ t in (0 : ℝ)..z,
        HighGaussianKernel.k186.realProfile.eval t * Real.exp (-(9 / 4 : ℝ) * t) := by
  apply high_gamma_decay_nonneg .k186 (show (profileCorrectionEnd .k186 : ℝ) ≤ z from hz)
  simpa only [profileCorrectionEnd, Rat.cast_ofNat, Rat.cast_div, Int.cast_ofNat, Int.cast_natCast,
    Nat.cast_ofNat] using k186_gamma_decay_endpoint

/-- Beyond the two profile cutoffs, the decaying moment contributes at most
zero for K186 and 806 for K196, before multiplication by its H33 weight. -/
theorem high_gamma_decay_tail_cap (K : HighGaussianKernel) {z : ℝ}
    (hz : (profileCorrectionEnd K : ℝ) ≤ z) :
    max (-(∫ t in (0 : ℝ)..z, K.realProfile.eval t * Real.exp (-((K.pole : ℝ) - 1 / 2) * t))) 0 ≤
      match K with
      | .k186 => 0
      | .k196 => 806 := by
  cases K
  · have h := k186_gamma_decay_tail hz
    norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]
    exact max_le (neg_nonpos.mpr h) le_rfl
  · have h := k196_gamma_decay_tail hz
    norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]
    exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
