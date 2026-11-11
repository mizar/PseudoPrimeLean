/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenAnchors
public import PseudoPrime.PrimeTestBounds.MillerRabin.TotalFactorWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.MixedTwoAdicLogBounds

/-! # Small-index local witnesses for the coefficient 0.28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational logarithm certificate bounds the logarithm of the finite-index
threshold used in the 0.28 middle-range argument. -/
theorem target028_log_index_bound : Real.log (50000000 : ℝ) ≤ 2216 / 125 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 50000000 26 32 17 (2216 / 125) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  exact h

/-- A divisor whose square is at most 50000000 times the input has the
logarithmic size required by the radius-48 local witness. -/
theorem target028_local_log {n q : ℕ} (hn : 0 < n) (hq : 0 < q) (hsize : q ^ 2 ≤ 50000000 * n) :
    Real.log q ≤ (Real.log n + 2216 / 125) / 2 := by
  have hR : (q : ℝ) ^ 2 ≤ (50000000 : ℝ) * n := by exact_mod_cast hsize
  have hl := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hq) 2) hR
  rw [Real.log_pow, Real.log_mul (by norm_num only) (Nat.cast_pos.mpr hn).ne'] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl, target028_log_index_bound]

end PseudoPrime.PrimeTestBounds.MillerRabin
