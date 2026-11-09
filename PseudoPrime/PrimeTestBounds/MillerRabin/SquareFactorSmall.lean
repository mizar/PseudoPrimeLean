/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Small square-divisor logarithmic bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If `p²` divides a positive input with logarithm at most 8.3, then
`p ≤ 64`. A rational lower certificate for `log 4096` bounds the input and
the divisibility relation bounds the square. -/
theorem square_factor_le_64 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (83 / 10 : ℝ)) : p ≤ 64 := by
  have h4096 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 4096 12 32 (83 / 10) 9 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h4096
  have hnle : n ≤ 4096 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (4096 : ℝ) := hU.trans h4096
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 4096)).mp
        hlog
  have hpsq : p ^ 2 ≤ 4096 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- The budget `45/10` is below the logarithm of `p²` whenever `p > 19`.
The certified lower bound for `log 20` and logarithm monotonicity supply the
strict product-size condition for the first weighted square-factor cell. -/
theorem square_factor_budget_45 {p : ℕ} (hbig : 19 < p) :
    (45 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h20 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 20 5 32 (29 / 10) 3 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h20
  have hp20 : 20 ≤ p := Nat.succ_le_of_lt hbig
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 20) (Nat.cast_le.mpr hp20)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h20, hl]

end PseudoPrime.PrimeTestBounds.MillerRabin
