/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerGain663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerGain663

/-! # Shared recovered powers for the three K137 cells -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem k137_power_min : ∀ n ∈ fixedPowers663, 110889 < n := by decide +kernel

/-- All powers from the existing list stay above the cutoff and within the
principal kernel support up to radius 333. -/
theorem gaussian_k137_power_support {r : ℝ} (hr : r ∈ Set.Icc 328 333) {n : ℕ}
    (hn : n ∈ fixedPowers663) : r ^ 2 < (n : ℝ) ∧ Real.log ((n : ℝ) / r ^ 2) < 21 / 8 := by
  have h325 : (325 : ℝ) ≤ r := by linarith only [hr.1]
  have hpos : 0 < r := by linarith only [h325]
  have hn' : (110889 : ℝ) < n := by exact_mod_cast k137_power_min n hn
  have hsq := pow_le_pow_left₀ hpos.le hr.2 2
  have ht : r ^ 2 < (n : ℝ) := by linarith only [hsq, hn']
  have hp := (sq_nonneg r).trans_lt ht
  have hmono :=
    div_le_div_of_nonneg_left hp.le (by norm_num only : (0 : ℝ) < 325 ^ 2)
      (pow_le_pow_left₀ (by norm_num only) h325 2)
  have h₀ := fixed_power_support_663 (r := 325) ⟨le_rfl, by norm_num only⟩ hn
  exact ⟨ht, (Real.log_le_log (div_pos hp (sq_pos_of_pos hpos)) hmono).trans_lt h₀.2⟩

/-- The previously certified weighted gain remains available up to radius
333, including the last two compressed K137 cells. -/
theorem gaussian_k137_power_gain {r : ℝ} (hr : r ∈ Set.Icc 328 333) :
    0.137116529 ≤
      ∑ n ∈ fixedPowers663,
        4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  refine fixed_power_gain_at_325.trans (Finset.sum_le_sum fun n hn ↦ ?_)
  have ha : (325 : ℝ) ≤ r := by linarith only [hr.1]
  have hs := gaussian_k137_power_support hr hn
  have h₀ := fixed_power_support_663 (r := 325) ⟨le_rfl, by norm_num only⟩ hn
  exact
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (weight_radius_mono (by norm_num only) ha hs.1.le h₀.2.le)
        ArithmeticFunction.vonMangoldt_nonneg)
      (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
