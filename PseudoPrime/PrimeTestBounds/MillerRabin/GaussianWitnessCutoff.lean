/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Scalar bounds for the Gaussian witness cutoff -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For log input `L`, take the maximum of two, the quarter-square floor and the
Gaussian-corrected quadratic bound used by the 027p criterion. -/
@[expose]
noncomputable def gaussianWitnessCutoff (L : ℝ) : ℝ :=
  max 2
    (max ((1 / 4 : ℝ) * L ^ 2)
      ((9090 / 33659 : ℝ) * L ^ 2 - (53 / 4 : ℝ) * L * Real.exp (-(L / 11000) ^ 2)))

/-- For a positive logarithm, the Gaussian cutoff equals the squared half-logarithm
exactly when both the floor two and the Gaussian branch lie below it. Cancelling the
positive logarithm gives the scalar inequality that determines the upper endpoint. -/
theorem gaussianCutoff_quarter_iff {L : ℝ} (hL : 0 < L) :
    gaussianWitnessCutoff L = (L / 2) ^ 2 ↔
      2 ≤ (L / 2) ^ 2 ∧ (9090 / 33659 - 1 / 4 : ℝ) * L ≤ 53 / 4 * Real.exp (-(L / 11000) ^ 2) := by
  have he : (1 / 4 : ℝ) * L ^ 2 = (L / 2) ^ 2 := by ring
  have hb : (L / 2) ^ 2 ≤ gaussianWitnessCutoff L := by
    rw [← he]
    exact (le_max_left _ _).trans (le_max_right _ _)
  rw [le_antisymm_iff, and_iff_left hb]
  unfold gaussianWitnessCutoff
  rw [max_le_iff, max_le_iff, he, and_iff_right (le_refl _)]
  apply and_congr_right
  intro _
  conv_rhs => rw [← mul_le_mul_iff_left₀ hL]
  constructor <;> intro h <;> linarith only [h]

/-- The quarter branch is active throughout the interval from 3 to 658.
The exponential tangent at zero supplies a uniform lower bound for the deficit. -/
theorem gaussianCutoff_quarter_to658 {L : ℝ} (hl : 3 ≤ L) (hu : L ≤ 658) :
    gaussianWitnessCutoff L = (L / 2) ^ 2 := by
  have hp : 0 < L := by linarith only [hl]
  apply (gaussianCutoff_quarter_iff hp).mpr
  constructor
  · nlinarith only [hl, sq_nonneg (L - 3)]
  · have ht := Real.add_one_le_exp (-((L / 11000) ^ 2))
    nlinarith only [ht, hu, mul_nonneg hp.le (sub_nonneg.mpr hu)]

/-- Every positive log input at which the quarter branch is active is below 663.
Thus the closed quarter-witness interval in the manuscript covers the switch itself. -/
theorem log_lt_663_of_gaussian_quarter {L : ℝ} (hl : 0 < L)
    (hq : gaussianWitnessCutoff L = (L / 2) ^ 2) : L < 663 := by
  have he := (gaussianCutoff_quarter_iff hl).mp hq
  have hb := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg (L / 11000)))
  linarith only [he.2, hb]

/-- From log 663 onward the Gaussian quadratic exceeds both cutoff floors.
This gives the explicit cutoff used in the large-radius comparisons. -/
theorem gaussianCutoff_eq_quadratic {L : ℝ} (hL : 663 ≤ L) :
    gaussianWitnessCutoff L = 9090 / 33659 * L ^ 2 - 53 / 4 * L * Real.exp (-(L / 11000) ^ 2) := by
  have hp : 0 < L := by linarith only [hL]
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg (L / 11000)))
  have hd : 0 ≤ (9090 / 33659 - 1 / 4 : ℝ) * L - 53 / 4 * Real.exp (-(L / 11000) ^ 2) := by
    linarith only [he, hL]
  have hq :
    (1 / 4 : ℝ) * L ^ 2 ≤ 9090 / 33659 * L ^ 2 - 53 / 4 * L * Real.exp (-(L / 11000) ^ 2) := by
    nlinarith only [mul_nonneg hp.le hd]
  have htwo : (2 : ℝ) ≤ (1 / 4 : ℝ) * L ^ 2 := by
    nlinarith only [pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 663) hL 2]
  rw [gaussianWitnessCutoff, max_eq_right hq, max_eq_right (htwo.trans hq)]

/-- Beyond log 663 the cutoff divided by the squared logarithm increases.
The Gaussian deficit decreases because both the exponential and reciprocal decrease. -/
theorem gaussianCutoff_ratio_mono :
    MonotoneOn (fun L : ℝ ↦ gaussianWitnessCutoff L / L ^ 2) (Set.Ici 663) := by
  intro a ha b hb hab
  have ha' : (663 : ℝ) ≤ a := ha
  have hb' : (663 : ℝ) ≤ b := hb
  have ap : 0 < a := by linarith only [ha']
  have hratio (L : ℝ) (hl : 663 ≤ L) (hp : 0 < L) :
    gaussianWitnessCutoff L / L ^ 2 =
      9090 / 33659 - (53 / 4) * (Real.exp (-(L / 11000) ^ 2) / L) := by
    rw [gaussianCutoff_eq_quadratic hl]
    field_simp [hp.ne']
  change gaussianWitnessCutoff a / a ^ 2 ≤ gaussianWitnessCutoff b / b ^ 2
  rw [hratio a ha' ap, hratio b hb' (ap.trans_le hab)]
  have he : Real.exp (-(b / 11000) ^ 2) ≤ Real.exp (-(a / 11000) ^ 2) :=
    Real.exp_le_exp.mpr
      (neg_le_neg
        (pow_le_pow_left₀ (div_nonneg ap.le (by norm_num only))
          (div_le_div_of_nonneg_right hab (by norm_num only)) 2))
  have hd := div_le_div_of_nonneg_left (Real.exp_pos (-(b / 11000) ^ 2)).le ap hab
  have h := hd.trans (div_le_div_of_nonneg_right he ap.le)
  linarith only [h]

/-- A rational upper bound for the exponential at the left endpoint of a
Gaussian cell certifies the fixed squared cutoff throughout the cell.
The kernel evaluated at the fixed scale may use this cutoff to bound its witnesses. -/
theorem gaussianCell_cutoff_le {a L c scale E : ℝ} (ha : 663 ≤ a) (hL : a ≤ L)
    (he : Real.exp (-(a / 11000) ^ 2) ≤ E) (hc : c ≤ 9090 / 33659 - 53 / 4 * E / a)
    (hs : scale ^ 2 ≤ 4 * c) : (scale * L / 2) ^ 2 ≤ gaussianWitnessCutoff L := by
  have ap : 0 < a := by linarith only [ha]
  have lp : 0 < L := ap.trans_le hL
  have he' :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num only : (0 : ℝ) ≤ 53 / 4))
      ap.le
  have h1 : c ≤ gaussianWitnessCutoff a / a ^ 2 := by
    rw [gaussianCutoff_eq_quadratic ha]
    have h := hc.trans (sub_le_sub_left he' (9090 / 33659))
    convert h using 1
    field_simp [ap.ne']
  have h2 := h1.trans (gaussianCutoff_ratio_mono ha (ha.trans hL) hL)
  have h3 := (le_div_iff₀ (sq_pos_of_pos lp)).1 h2
  nlinarith only [h3, mul_le_mul_of_nonneg_right hs (sq_nonneg L)]

/-- A positive rational Taylor certificate for the reciprocal exponential
supplies the exponential input to the Gaussian cell cutoff comparison. -/
theorem gaussianCell_cutoff_of_taylor {a L c scale E : ℝ} {N : ℕ} (ha : 663 ≤ a) (hL : a ≤ L)
    (hE : 0 ≤ E) (hT : 1 ≤ E * ∑ k ∈ Finset.range N, ((a / 11000) ^ 2) ^ k / k.factorial)
    (hc : c ≤ 9090 / 33659 - 53 / 4 * E / a) (hs : scale ^ 2 ≤ 4 * c) :
    (scale * L / 2) ^ 2 ≤ gaussianWitnessCutoff L := by
  apply gaussianCell_cutoff_le ha hL _ hc hs
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  exact
    hT.trans (mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (sq_nonneg (a / 11000)) N) hE)

/-- The first K137 cell uses the recorded scale at log 663. The same cutoff
bound holds throughout the cell by monotonicity of the normalized cutoff. -/
theorem gaussianCutoff_k137_first {L : ℝ} (hL : 663 ≤ L) :
    ((250074514713 / 250000000000 : ℝ) * L / 2) ^ 2 ≤ gaussianWitnessCutoff L := by
  let E : ℝ :=
    212659906806614960000000000000000000000000000000000000000000 /
      213433863031117672939952812279130842502951625360138114022121
  apply
    gaussianCell_cutoff_of_taylor (a := 663) (N := 8) (E := E) (c :=
      (250074514713 / 250000000000 : ℝ) ^ 2 / 4) (le_refl _) hL
  all_goals
    norm_num only [E, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one]

/-- On nonnegative logarithms the Gaussian cutoff is at most the three-elevenths
cutoff. The correction is nonnegative and both quadratic coefficients are smaller. -/
theorem gaussianCutoff_le_threeEleven {L : ℝ} (hL : 0 ≤ L) :
    gaussianWitnessCutoff L ≤ max 2 ((3 / 11 : ℝ) * L ^ 2) := by
  apply max_le_max_left
  apply max_le
  · exact mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg L)
  · apply
      le_trans (sub_le_self _ (mul_nonneg (mul_nonneg (by norm_num only) hL) (Real.exp_pos _).le))
    exact mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg L)

/-- For every log input at least 8000 the previous Gaussian envelope with parameters
8 and one million is below the target cutoff. The difference of the two squared
arguments exceeds 0.52, which gives the required exponential ratio. -/
theorem gaussian_old_cutoff_le {L : ℝ} (hL : 8000 ≤ L) :
    max 2
        (max ((1 / 4 : ℝ) * L ^ 2)
          ((9090 / 33659 : ℝ) * L ^ 2 - 8 * L * Real.exp (-(L / 1000000) ^ 2))) ≤
      gaussianWitnessCutoff L := by
  have hsq := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 8000) hL 2
  have hd : (52 / 100 : ℝ) ≤ (L / 11000) ^ 2 - (L / 1000000) ^ 2 := by nlinarith only [hsq]
  have ht := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 52 / 100) 4
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ht
  have he : (53 / 32 : ℝ) ≤ Real.exp ((L / 11000) ^ 2 - (L / 1000000) ^ 2) :=
    (by linarith only [ht] : (53 / 32 : ℝ) ≤ Real.exp (52 / 100)).trans (Real.exp_le_exp.mpr hd)
  rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _)] at he
  have hr : (53 / 32 : ℝ) * Real.exp (-(L / 11000) ^ 2) ≤ Real.exp (-(L / 1000000) ^ 2) := by
    rw [Real.exp_neg, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), ←
      div_eq_inv_mul, le_div_iff₀ (Real.exp_pos _)]
    exact he
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 8 * L by linarith only [hL])
  unfold gaussianWitnessCutoff
  apply max_le_max_left
  apply max_le_max_left
  linarith only [hm]

end PseudoPrime.PrimeTestBounds.MillerRabin
