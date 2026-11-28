/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleExp
import PseudoPrime.Analysis.ExponentialFixedPointBounds

/-! # A common dyadic exponential grid for the finite K186 tests -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The common positive integer scale for the high-range dyadic grid. -/
@[expose]
public def k186GapExpScale : ℤ :=
  10 ^ 88

/-- Adjacent outward decimal ticks for the exponential at 1/128. -/
private def expSeed : Analysis.IntegerInterval :=
  ⟨10078430972064479776934535597601235791933921498840372315421080289416115889044768157172574,
    10078430972064479776934535597601235791933921498840372315421080289416115889044768157172575⟩

/-- The rational Taylor subtotal for the seed. -/
private def expSubtotal : ℚ :=
  ∑ j ∈ Finset.range 36, (1 / 128 : ℚ) ^ j / (j.factorial : ℚ)

/-- Check the seed once using the first 36 Taylor terms and a geometric tail. -/
private theorem exp_seed_contains : expSeed.Contains k186GapExpScale (Real.exp (1 / 128)) := by
  have hl : (expSeed.lower : ℚ) / k186GapExpScale ≤ expSubtotal := by decide +kernel
  have hu :
    expSubtotal + (1 / 128 : ℚ) ^ 36 / (Nat.factorial 36 : ℚ) * 2 ≤
      (expSeed.upper : ℚ) / k186GapExpScale := by
    decide +kernel
  have hl' := (Rat.cast_le (K := ℝ)).mpr hl
  have hu' := (Rat.cast_le (K := ℝ)).mpr hu
  simp only [expSubtotal, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_intCast, Rat.cast_ofNat, Rat.cast_one] at hl' hu'
  exact
    ⟨hl'.trans (Real.sum_le_exp_of_nonneg (by norm_num only) 36),
      (Analysis.exp_le_taylor_add_two_next (by norm_num only) (by norm_num only)).trans hu'⟩

/-- A binary fixed-point enclosure at a nonnegative multiple of 1/128. -/
public def k186GapExp (n : ℕ) : Analysis.IntegerInterval :=
  gaussianMidExpFold k186GapExpScale n ⟨k186GapExpScale, k186GapExpScale⟩ expSeed

/-- Interpret the positive grid value without any per-cell Taylor expansion. -/
public theorem k186_gap_exp_contains (n : ℕ) :
    (k186GapExp n).Contains k186GapExpScale (Real.exp ((n : ℝ) / 128)) := by
  have ho :
    (Analysis.IntegerInterval.mk k186GapExpScale k186GapExpScale).Contains k186GapExpScale 1 := by
    constructor <;> norm_num only [k186GapExpScale]
  have h :=
    gaussian_mid_exp_fold_contains (by decide +kernel : 0 < k186GapExpScale) n ho exp_seed_contains
  simpa only [k186GapExp, one_mul, ← Real.exp_natCast_mul, mul_one_div] using h

/-- The signed grid uses the reciprocal of the same positive computation. -/
public def k186GapExpNeg (n : ℕ) : Analysis.IntegerInterval :=
  gaussianMidScaledInv k186GapExpScale 1 (k186GapExp n)

/-- Interpret a negative grid value when its positive input ticks are positive. -/
public theorem k186_gap_exp_neg_contains (n : ℕ) (hn : 0 < (k186GapExp n).lower) :
    (k186GapExpNeg n).Contains k186GapExpScale (Real.exp (-((n : ℝ) / 128))) := by
  have h :=
    gaussian_mid_scaled_inv (by decide +kernel : 0 < k186GapExpScale) (by decide : (0 : ℤ) ≤ 1) hn
      (k186_gap_exp_contains n)
  simpa only [k186GapExpNeg, Real.exp_neg, Int.cast_one, one_div] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
