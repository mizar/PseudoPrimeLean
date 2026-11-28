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

/-- Outward rounding preserves the scale as a lower bound for positive products. -/
private theorem product_lower_ge {G : ℤ} (hG : 0 < G) {A B : Analysis.IntegerInterval}
    (ha : G ≤ A.lower) (ha' : G ≤ A.upper) (hb : G ≤ B.lower) (hb' : G ≤ B.upper) :
    G ≤ (Analysis.roundedProduct G A B).lower := by
  change G ≤ _ / G
  apply (Int.le_ediv_iff_mul_le hG).mpr
  exact
    le_min
      (le_min (mul_le_mul ha hb hG.le (hG.le.trans ha)) (mul_le_mul ha hb' hG.le (hG.le.trans ha)))
      (le_min (mul_le_mul ha' hb hG.le (hG.le.trans ha'))
        (mul_le_mul ha' hb' hG.le (hG.le.trans ha')))

/-- If all input ticks are at least the scale, both product ticks are too. -/
private theorem product_ticks_ge {G : ℤ} (hG : 0 < G) {A B : Analysis.IntegerInterval}
    (ha : G ≤ A.lower ∧ G ≤ A.upper) (hb : G ≤ B.lower ∧ G ≤ B.upper) :
    G ≤ (Analysis.roundedProduct G A B).lower ∧ G ≤ (Analysis.roundedProduct G A B).upper := by
  refine ⟨product_lower_ge hG ha.1 ha.2 hb.1 hb.2, ?_⟩
  have h :=
    Int.ediv_mul_le
      (-(max (max (A.lower * B.lower) (A.lower * B.upper))
          (max (A.upper * B.lower) (A.upper * B.upper))))
      (ne_of_gt hG)
  apply le_of_mul_le_mul_right _ hG
  exact
    (mul_le_mul ha.1 hb.1 hG.le (hG.le.trans ha.1)).trans
      ((le_max_left _ _).trans
        ((le_max_left _ _).trans
          (by
            simpa only [Analysis.roundedProduct, Analysis.roundInterval, neg_mul, neg_neg] using
              neg_le_neg h)))

/-- Binary accumulation preserves the lower bound on both interval ticks. -/
private theorem fold_ticks_ge {G : ℤ} (hG : 0 < G) (n : ℕ) {A B : Analysis.IntegerInterval}
    (ha : G ≤ A.lower ∧ G ≤ A.upper) (hb : G ≤ B.lower ∧ G ≤ B.upper) :
    G ≤ (gaussianMidExpFold G n A B).lower ∧ G ≤ (gaussianMidExpFold G n A B).upper := by
  induction n using Nat.strong_induction_on generalizing A B with
  | ind n ih =>
    by_cases hn : n = 0
    · rw [gaussianMidExpFold, dite_eq_left hn]
      exact ha
    rw [gaussianMidExpFold, dite_eq_right hn]
    refine
      ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)) ?_
        (product_ticks_ge hG hb hb)
    split
    · exact ha
    · exact product_ticks_ge hG ha hb

/-- Every positive-grid enclosure has a strictly positive lower tick.
The seed and the unit interval start at or above the scale. -/
public theorem k186_gap_exp_lower_pos (n : ℕ) : 0 < (k186GapExp n).lower := by
  have hG : 0 < k186GapExpScale := by decide +kernel
  have hb : k186GapExpScale ≤ expSeed.lower ∧ k186GapExpScale ≤ expSeed.upper := by decide +kernel
  exact hG.trans_le (fold_ticks_ge hG n ⟨le_rfl, le_rfl⟩ hb).1

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
