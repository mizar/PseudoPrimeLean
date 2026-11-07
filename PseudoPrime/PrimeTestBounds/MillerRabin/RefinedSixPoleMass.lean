/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleKernel
public import PseudoPrime.LLS.PaperStatements.RationalPoleCutoff
public import PseudoPrime.Analysis.ExponentialFixedPointBounds

/-! # Exact principal mass of the refined sixth-pole kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The admissible normalized sixth-pole kernel has mass `3/16`.
The general sixth-order Cauchy integral is independent of the parameters. -/
theorem refined_six_pole_mass : refinedSixPoleKernel.mass = 3 / 16 := by
  exact LLS.PaperStatements.rationalPole_six_mass (by norm_num only) (by norm_num only)

/-- The refined kernel's value at one half has the displayed exact rational
coefficient of `exp(21/16)`. This is the subtracted endpoint contribution. -/
theorem refined_six_pole_half :
    (refinedSixPoleKernel.function (1 / 2)).re =
      (22958251200 / 243087455521 : ℝ) * Real.exp (21 / 16) := by
  rw [refinedSixPoleKernel, LLS.PaperStatements.rationalPole_half_value]
  norm_num only
  ring

/-- The refined kernel's unit-cutoff integral is an explicit rational
multiple of `exp(-567/200)`. The general logarithmic-moment formula evaluates
the six finite terms without numerical integration. -/
theorem refined_six_pole_cutoff :
    (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u) =
      (283259032134555769153731 / 62230388613376000000000 : ℝ) * Real.exp (-(567 / 200)) := by
  rw [refinedSixPoleKernel,
    LLS.PaperStatements.rationalPole_cutoff_moment _ _ _ _ (by norm_num only)]
  norm_num only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.choose_zero_right, Nat.choose_self, Nat.choose_one_right, Nat.choose,
    Nat.factorial, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  ring

/-- A finite Taylor envelope gives the positive exponential upper bound
needed to bound the unit-cutoff mass from below. -/
theorem refined_six_pole_exp_cutoff : Real.exp (567 / 200 : ℝ) ≤ 170305 / 10000 := by
  have ht :=
    Analysis.exp_le_taylor_add_two_next (x := (567 / 200 : ℝ)) (n := 16) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ht
  linarith only [ht]

/-- A finite Taylor envelope gives the exponential upper bound needed for the
half-point contribution. -/
theorem refined_six_pole_exp_half : Real.exp (21 / 16 : ℝ) ≤ 185773 / 50000 := by
  have ht :=
    Analysis.exp_le_taylor_add_two_next (x := (21 / 16 : ℝ)) (n := 12) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ht
  linarith only [ht]

/-- The actual normalized unit-cutoff integral is at least 0.26727. -/
theorem refined_six_pole_cutoff_lower :
    (26727 / 100000 : ℝ) ≤
      ∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u := by
  rw [refined_six_pole_cutoff, Real.exp_neg, ← one_div]
  have h := one_div_le_one_div_of_le (Real.exp_pos (567 / 200 : ℝ)) refined_six_pole_exp_cutoff
  have hm :=
    mul_le_mul_of_nonneg_left h
      (by norm_num only : (0 : ℝ) ≤ 283259032134555769153731 / 62230388613376000000000)
  norm_num only at hm ⊢
  linarith only [hm]

/-- The actual normalized value at one half is at most 0.35091. -/
theorem refined_six_pole_half_upper :
    (refinedSixPoleKernel.function (1 / 2)).re ≤ (35091 / 100000 : ℝ) := by
  rw [refined_six_pole_half]
  have h :=
    mul_le_mul_of_nonneg_left refined_six_pole_exp_half
      (by norm_num only : (0 : ℝ) ≤ 22958251200 / 243087455521)
  norm_num only at h ⊢
  linarith only [h]

/-- The normalized leading coefficient obtained from the actual sixth-pole
mass, cutoff integral and endpoint is strictly below 0.273. This certifies
only the asymptotic principal ratio; finite-scale error terms require separate
bounds before it can yield a witness theorem. -/
theorem refined_six_pole_leading_ratio :
    (2 * refinedSixPoleKernel.mass /
          (4 * (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u) -
            (refinedSixPoleKernel.function (1 / 2)).re)) ^
        2 <
      (273 / 1000 : ℝ) := by
  let D : ℝ :=
    4 * (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u) -
      (refinedSixPoleKernel.function (1 / 2)).re
  have hD : (71817 / 100000 : ℝ) ≤ D := by
    dsimp only [D]
    linarith only [refined_six_pole_cutoff_lower, refined_six_pole_half_upper]
  have hratio : (3 / 8 : ℝ) / D ≤ (3 / 8 : ℝ) / (71817 / 100000) :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hD
  have hnonneg : 0 ≤ (3 / 8 : ℝ) / D :=
    div_nonneg (by norm_num only) ((by norm_num only : (0 : ℝ) ≤ 71817 / 100000).trans hD)
  have hs := pow_le_pow_left₀ hnonneg hratio 2
  rw [refined_six_pole_mass]
  norm_num only
  exact hs.trans_lt (by norm_num only)

/-- On the critical line the refined kernel norm is the sixth-order
resolvent with pole `27/25`, including the exact normalization factor.
This identifies the actual zero-series weight for the differentiated Poisson
identity needed in the high-range estimate. -/
theorem refined_six_pole_norm (t : ℝ) :
    ‖refinedSixPoleKernel.function (Complex.I * t)‖ =
      (27 / 25 : ℝ) ^ 5 / ((27 / 25 : ℝ) ^ 2 + t ^ 2) ^ 3 := by
  change ‖Analysis.rationalPoleFunction 3 (25 / 54) (21 / 16) (Complex.I * t)‖ = _
  rw [Analysis.norm_rationalPoleFunction 3 (by norm_num only : (0 : ℝ) < 25 / 54)]
  have h : (27 / 25 : ℝ) ^ 2 + t ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num only) (sq_nonneg t))
  have hd : 1 + (2 * (25 / 54 : ℝ) * t) ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num only) (sq_nonneg _))
  apply (div_eq_div_iff (pow_ne_zero 3 hd) (pow_ne_zero 3 h)).2
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
