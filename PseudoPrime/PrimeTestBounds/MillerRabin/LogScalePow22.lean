/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds

/-! # A certified logarithmic upper bound for the finite classification -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Logarithmic scale at most `15.2` still lies below `2^22`. The stronger
rational logarithm certificate extends the complete finite classification. -/
theorem le_pow22_of_log_le_152 {n : ℕ} (hn : 1 < n) (hU : Real.log n ≤ (76 / 5 : ℝ)) :
    n ≤ 2 ^ 22 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 4194304 23 32 (76 / 5) 16 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hlog : Real.log (n : ℝ) ≤ Real.log (4194304 : ℝ) := by linarith only [hU, hcert]
  have hcast :=
    (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
          (by norm_num only : (0 : ℝ) < 4194304)).mp
      hlog
  norm_num only at hcast ⊢
  exact_mod_cast hcast

end PseudoPrime.PrimeTestBounds.MillerRabin
