/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaExpRationalBounds

/-! # Exponential bounds for the high Gaussian convolution endpoints -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A finite reciprocal Taylor sum, rescaled by sixteen, bounds the
negative exponential finely enough for the high convolution endpoints. -/
def gammaConvExpUpper (x : ℚ) (N : ℕ) : ℚ :=
  ((∑ i ∈ Finset.range N, (x / 16) ^ i / (i.factorial : ℚ))⁻¹) ^ 16

/-- The rescaled rational Taylor upper bound encloses the true exponential
for every nonnegative rational input. -/
theorem gamma_conv_exp_upper_valid {x : ℚ} (hx : 0 ≤ x) {N : ℕ} (hN : 0 < N) :
    Real.exp (-(x : ℝ)) ≤ (gammaConvExpUpper x N : ℝ) := by
  let t : ℝ := (x : ℝ) / 16
  have ht : 0 ≤ t := div_nonneg (Rat.cast_nonneg.mpr hx) (by norm_num only)
  let S := ∑ i ∈ Finset.range N, t ^ i / (i.factorial : ℝ)
  have hS : 0 < S := by
    have h :=
      Finset.single_le_sum (s := Finset.range N) (f := fun i ↦ t ^ i / (i.factorial : ℝ))
        (fun i _ ↦ div_nonneg (pow_nonneg ht _) (Nat.cast_nonneg _)) (Finset.mem_range.mpr hN)
    exact
      zero_lt_one.trans_le
        (by simpa only [S, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] using h)
  have he : Real.exp (-t) ≤ S⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hS).mpr (Real.sum_le_exp_of_nonneg ht N)
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le he 16
  rw [← Real.exp_natCast_mul] at hp
  have harg : (16 : ℝ) * -t = -(x : ℝ) := by
    dsimp only [t]; ring
  rw [Nat.cast_ofNat, harg] at hp
  simpa only [gammaConvExpUpper, Rat.cast_pow, Rat.cast_inv, Rat.cast_sum, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_ofNat, S, t] using hp

end PseudoPrime.PrimeTestBounds.MillerRabin
