/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel644
import PseudoPrime.Analysis.ExponentialFixedPointBounds

/-! # Linear comparison coefficient for section 122 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem shift122_exp_box {x l u : ℝ} (hx : 0 ≤ x) (hs : x / 33 ≤ 1 / 2)
    (hl : l ≤ ∑ k ∈ Finset.range 32, x ^ k / (k.factorial : ℝ))
    (hu :
      (∑ k ∈ Finset.range 32, x ^ k / (k.factorial : ℝ)) + (x ^ 32 / ((32 : ℕ).factorial : ℝ)) * 2 ≤
        u) :
    l ≤ Real.exp x ∧ Real.exp x ≤ u := by
  exact
    ⟨hl.trans (Real.sum_le_exp_of_nonneg hx _),
      (Analysis.exp_le_taylor_add_two_next (x := x) (n := 32) hx hs).trans hu⟩

private theorem shift122_inv_box {x l u : ℝ} (hl : 0 < l) (h : l ≤ Real.exp x ∧ Real.exp x ≤ u) :
    1 / u ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ 1 / l := by
  rw [Real.exp_neg, ← one_div]
  exact ⟨one_div_le_one_div_of_le (Real.exp_pos _) h.2, one_div_le_one_div_of_le hl h.1⟩

/-- The normalized cosine conductor profile at a nonnegative shift. -/
noncomputable def threeShiftG122 (s : ℝ) : ℝ :=
  2 * Real.exp (-((107 / 100 : ℝ) * s)) *
    (3 / 8 + 3 * (107 / 100) / 8 * s + (107 / 100) ^ 2 / 8 * s ^ 2)

/-- The coefficient of r from the cosine conductor and shifted symmetric poles
in the section 122 comparison. -/
noncomputable def threeShiftGain122 : ℝ :=
  1.54 * threeShiftG122 (2687 / 1000) - 1.508 * threeShiftG122 (2707 / 1000) -
        0.0917 * threeShiftG122 (3787 / 1000) -
        ((1.54 ^ 2 + 1.508 ^ 2 + 0.0917 ^ 2) / 2) * threeShiftG122 0 +
      (1.54 * 1.508) * threeShiftG122 (1 / 50) +
      (1.54 * 0.0917) * threeShiftG122 (11 / 10) -
    (1.508 * 0.0917) * threeShiftG122 (27 / 25) -
    (3 * (107 / 100) ^ 5 / (157 / 100) ^ 6) *
      (1.54 - 1.508 * Real.exp (-(1 / 100)) - 0.0917 * Real.exp (-(11 / 20)))

/-- Rational Taylor intervals certify the section 122 linear gain. -/
theorem three_shift_gain_lower122 : 0.00063602 < threeShiftGain122 := by
  have k0 :=
    shift122_exp_box (x := 1 / 100) (l := 1010050167083 / 10 ^ 12) (u := 1010050167086 / 10 ^ 12)
      (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have m0 := shift122_inv_box (by norm_num only) k0
  have k1 :=
    shift122_exp_box (x := 11 / 20) (l := 1733253017866 / 10 ^ 12) (u := 1733253017869 / 10 ^ 12)
      (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have m1 := shift122_inv_box (by norm_num only) k1
  have h0 :=
    shift122_exp_box (x := (107 / 100) * (1 / 50)) (l := 1021630622165 / 10 ^ 12) (u :=
      1021630622168 / 10 ^ 12) (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have j0 := shift122_inv_box (by norm_num only) h0
  have h1 :=
    shift122_exp_box (x := (107 / 100) * (11 / 10)) (l := 3244625710330 / 10 ^ 12) (u :=
      3244625710333 / 10 ^ 12) (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have j1 := shift122_inv_box (by norm_num only) h1
  have h2 :=
    shift122_exp_box (x := (107 / 100) * (27 / 25)) (l := 3175928403015 / 10 ^ 12) (u :=
      3175928403018 / 10 ^ 12) (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have j2 := shift122_inv_box (by norm_num only) h2
  have h3 :=
    shift122_exp_box (x := (107 / 100) * (2687 / 1000)) (l := 17727019481421 / 10 ^ 12) (u :=
      17727019481424 / 10 ^ 12) (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have j3 := shift122_inv_box (by norm_num only) h3
  have h4 :=
    shift122_exp_box (x := (107 / 100) * (2707 / 1000)) (l := 18110465941968 / 10 ^ 12) (u :=
      18110465941971 / 10 ^ 12) (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have j4 := shift122_inv_box (by norm_num only) h4
  have h5 :=
    shift122_exp_box (x := (107 / 100) * (3787 / 1000)) (l := 57517543176965 / 10 ^ 12) (u :=
      57517543176968 / 10 ^ 12) (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have j5 := shift122_inv_box (by norm_num only) h5
  unfold threeShiftGain122 threeShiftG122
  norm_num only [mul_zero, neg_zero, Real.exp_zero, one_mul]
  linarith only [m0.1, m0.2, m1.1, m1.2, j0.1, j0.2, j1.1, j1.2, j2.1, j2.2, j3.1, j3.2, j4.1, j4.2,
    j5.1, j5.2]

/-- Subtracting the principal and auxiliary linear recoveries from the
three-character mass slope gives the section 122 comparison coefficient. -/
theorem quarter_effective_slope_644 :
    (3 / 4 : ℝ) -
        (4 * (∫ u : ℝ in (0 : ℝ)..1, (quarterKernel644.transform u).re / Real.sqrt u) -
          (quarterKernel644.function (1 / 2)).re) -
        threeShiftGain122 <
      0.03138163 := by
  linarith only [quarter_principal_delta_644, three_shift_gain_lower122]

end PseudoPrime.PrimeTestBounds.MillerRabin
