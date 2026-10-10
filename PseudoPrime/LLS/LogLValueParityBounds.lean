/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperDefinitions
public import Mathlib.Tactic

/-!
# Cancellation of parity corrections in logarithmic L-value bounds

Geometric estimates bound the even and odd reciprocal correction series.
For `x ≥ 100`, their contribution cancels the gamma endpoint constant and the
remaining error with the required sign in both logarithmic L-value inequalities.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For x >= 2 and natural a,k, bound the parity-tail term by x^(-2k-2).
Its two linear denominator factors have product at least one, and the extra
power a only enlarges the denominator. This gives a common geometric majorant. -/
private theorem parity_tail_term_le (x : ℝ) (hx : 2 ≤ x) (a k : ℕ) :
    1 / (x ^ (2 * k + 2 + a) * (2 * (k : ℝ) + 1 + a) * (2 * (k : ℝ) + 2 + a)) ≤
      1 / x ^ (2 * k + 2) := by
  have hx1 : 1 ≤ x := le_trans (by norm_num only) hx
  have hp := pow_pos (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx) (2 * k + 2)
  have he := pow_le_pow_right₀ hx1 (Nat.le_add_right (2 * k + 2) a)
  have hd : 1 ≤ (2 * (k : ℝ) + 1 + a) * (2 * (k : ℝ) + 2 + a) := by
    nlinarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  apply one_div_le_one_div_of_le hp
  have hm :=
    mul_le_mul_of_nonneg_left hd
      (pow_nonneg (le_trans (by norm_num only : (0 : ℝ) ≤ 2) hx) (2 * k + 2 + a))
  nlinarith only [he, hm]

/-- For x >= 2, the parity-tail family with natural shift a is nonnegative
and at most 1/(x^2-1). Apply a geometric majorant and evaluate its sum;
shifts zero and one give the odd and even corrections respectively. -/
theorem reciprocalParityTail_bounds (x : ℝ) (hx : 2 ≤ x) (a : ℕ) :
    0 ≤ (∑' k : ℕ, 1 / (x ^ (2 * k + 2 + a) * (2 * (k : ℝ) + 1 + a) * (2 * (k : ℝ) + 2 + a))) ∧
      (∑' k : ℕ, 1 / (x ^ (2 * k + 2 + a) * (2 * (k : ℝ) + 1 + a) * (2 * (k : ℝ) + 2 + a))) ≤
        1 / (x ^ 2 - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx
  have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
  have hib : x⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using (inv_le_inv₀ hx0 (by norm_num only : (0 : ℝ) < 2)).mpr hx
  have hr : x⁻¹ ^ 2 < 1 := by nlinarith only [hi, hib]
  have hg := (summable_geometric_of_lt_one (sq_nonneg x⁻¹) hr).mul_left (x⁻¹ ^ 2)
  have hn (k : ℕ) : 0 ≤ 1 / (x ^ (2 * k + 2 + a) * (2 * (k : ℝ) + 1 + a) * (2 * (k : ℝ) + 2 + a)) :=
    div_nonneg (by norm_num only)
      (mul_nonneg
        (mul_nonneg (pow_nonneg hx0.le _)
          (by linarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg a : (0 : ℝ) ≤ a)]))
        (by linarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg a : (0 : ℝ) ≤ a)]))
  have hb (k : ℕ) :
    1 / (x ^ (2 * k + 2 + a) * (2 * (k : ℝ) + 1 + a) * (2 * (k : ℝ) + 2 + a)) ≤
      x⁻¹ ^ 2 * (x⁻¹ ^ 2) ^ k := by
    apply (parity_tail_term_le x hx a k).trans_eq
    simp only [one_div, ← inv_pow]
    rw [show 2 * k + 2 = 2 + 2 * k by ring, pow_add, pow_mul]
  have hs := hg.of_nonneg_of_le hn hb
  constructor
  · exact tsum_nonneg hn
  · apply (hs.tsum_le_tsum hb hg).trans_eq
    rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg x⁻¹) hr]
    have hden : x ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hx] : 0 < x ^ 2 - 1)
    field_simp [ne_of_gt hx0, hden]

/-- For x >= 100, the even correction lies between -log 2-gamma/2 and that
constant plus (log x+1+gamma/2)/x. Bound its positive tail geometrically;
its omitted tail is smaller than the explicit positive correction. These
two estimates are used in the upper and lower parity cancellations. -/
theorem reciprocalCorrectionEven_bounds (x : ℝ) (hx : 100 ≤ x) :
    -Real.log 2 - Real.eulerMascheroniConstant / 2 ≤ reciprocalCorrectionEven x ∧
      reciprocalCorrectionEven x ≤
        -Real.log 2 - Real.eulerMascheroniConstant / 2 +
          (Real.log x + 1 + Real.eulerMascheroniConstant / 2) / x := by
  have hx2 : 2 ≤ x := le_trans (by norm_num only) hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 100) hx
  let S := ∑' k : ℕ, 1 / (x ^ (2 * (k + 1) + 1) * (2 * ((k : ℝ) + 1)) * (2 * ((k : ℝ) + 1) + 1))
  have hs : 0 ≤ S ∧ S ≤ 1 / (x ^ 2 - 1) := by
    have heq :
      S =
        ∑' k : ℕ,
          1 /
            (x ^ (2 * k + 2 + 1) * (2 * (k : ℝ) + 1 + (1 : ℕ)) * (2 * (k : ℝ) + 2 + (1 : ℕ))) := by
      apply tsum_congr
      intro k
      rw [show 2 * (k + 1) + 1 = 2 * k + 2 + 1 by ring]
      norm_num only [Nat.cast_one]
      ring
    rw [heq]
    exact reciprocalParityTail_bounds x hx2 1
  have ht : S ≤ 1 / (4 * x) :=
    hs.2.trans
      (one_div_le_one_div_of_le (by linarith only [hx0] : 0 < 4 * x) (by nlinarith only [hx]))
  have hl := Real.log_nonneg (le_trans (by norm_num only : (1 : ℝ) ≤ 100) hx)
  have hg := Real.one_half_lt_eulerMascheroniConstant
  rw [reciprocalCorrectionEven]
  change
    -Real.log 2 - Real.eulerMascheroniConstant / 2 * (1 - 1 / x) + (Real.log x + 1) / x - S ≥
        -Real.log 2 - Real.eulerMascheroniConstant / 2 ∧
      -Real.log 2 - Real.eulerMascheroniConstant / 2 * (1 - 1 / x) + (Real.log x + 1) / x - S ≤
        -Real.log 2 - Real.eulerMascheroniConstant / 2 +
          (Real.log x + 1 + Real.eulerMascheroniConstant / 2) / x
  constructor
  · have h := (le_div_iff₀ (by linarith only [hx0] : 0 < 4 * x)).mp ht
    field_simp [ne_of_gt hx0]
    nlinarith only [h, hl, hg, hx0]
  · have hn := hs.1
    field_simp [ne_of_gt hx0]
    nlinarith only [hn, hx0]

/-- For x >= 100, the odd correction lies between -gamma/2 and that constant
plus (log 2+gamma/2)/x. The positive tail is at most 1/(4x), which is
absorbed using gamma > 1/2. This supplies both signs of the odd correction. -/
theorem reciprocalCorrectionOdd_bounds (x : ℝ) (hx : 100 ≤ x) :
    -Real.eulerMascheroniConstant / 2 ≤ reciprocalCorrectionOdd x ∧
      reciprocalCorrectionOdd x ≤
        -Real.eulerMascheroniConstant / 2 +
          (Real.log 2 + Real.eulerMascheroniConstant / 2) / x := by
  have hx2 : 2 ≤ x := le_trans (by norm_num only) hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 100) hx
  let S := ∑' k : ℕ, 1 / (x ^ (2 * k + 2) * (2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2))
  have hs : 0 ≤ S ∧ S ≤ 1 / (x ^ 2 - 1) := by
    simpa only [Nat.cast_zero, add_zero] using reciprocalParityTail_bounds x hx2 0
  have ht : S ≤ 1 / (4 * x) :=
    hs.2.trans
      (one_div_le_one_div_of_le (by linarith only [hx0] : 0 < 4 * x) (by nlinarith only [hx]))
  have hl := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2)
  have hg := Real.one_half_lt_eulerMascheroniConstant
  change
    -S - Real.eulerMascheroniConstant / 2 * (1 - 1 / x) + Real.log 2 / x ≥
        -Real.eulerMascheroniConstant / 2 ∧
      -S - Real.eulerMascheroniConstant / 2 * (1 - 1 / x) + Real.log 2 / x ≤
        -Real.eulerMascheroniConstant / 2 + (Real.log 2 + Real.eulerMascheroniConstant / 2) / x
  constructor
  · have h := (le_div_iff₀ (by linarith only [hx0] : 0 < 4 * x)).mp ht
    field_simp [ne_of_gt hx0]
    nlinarith only [h, hl, hg, hx0]
  · have hn := hs.1
    field_simp [ne_of_gt hx0]
    nlinarith only [hn, hx0]

/-- For x >= 100, sqrt x >= 10 and 2 <= log x <= 3 sqrt x/5. The lower bound
uses log 16=4 log 2; the upper bound uses the tangent inequality for
log(sqrt x/4) and the known bound for log 2. These estimates control the
rational coefficients in both parity cases. -/
theorem sqrt_log_cutoff_bounds (x : ℝ) (hx : 100 ≤ x) :
    10 ≤ Real.sqrt x ∧ 2 ≤ Real.log x ∧ Real.log x ≤ 3 * Real.sqrt x / 5 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 100) hx
  have hy : (10 : ℝ) ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith only [hx])
  have hy0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hl :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 16)
      (le_trans (by norm_num only : (16 : ℝ) ≤ 100) hx)
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have ht := Real.log_le_sub_one_of_pos (div_pos hy0 (by norm_num only : (0 : ℝ) < 4))
  rw [Real.log_div (ne_of_gt hy0) (by norm_num only : (4 : ℝ) ≠ 0)] at ht
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  rw [h4, Real.log_sqrt hx0.le] at ht
  rw [h16] at hl
  exact
    ⟨hy, by linarith only [hl, Real.log_two_gt_d9], by linarith only [ht, hy, Real.log_two_lt_d9]⟩

/-- For y >= 10, l >= 2 and C >= 1/4, E >= -C makes the upper parity
combination nonpositive. Its coefficient is nonnegative and no larger
than 1/l-2/(y l^2); the remaining error is absorbed by C y >= 1. -/
private theorem upper_parity_cancellation (y l C E : ℝ) (hy : 10 ≤ y) (hl : 2 ≤ l) (hC : 1 / 4 ≤ C)
    (hE : -C ≤ E) :
    -E * ((1 / l - 2 / (y * l ^ 2)) / (1 + 1 / y) ^ 2) - C / l + 2 / (y ^ 2 * l ^ 2) ≤ 0 := by
  have hy0 : 0 < y := by linarith only [hy]
  have hl0 : 0 < l := by linarith only [hl]
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hi : 0 ≤ 1 / y := div_nonneg (by norm_num only) hy0.le
  have hc : 0 ≤ 1 / l - 2 / (y * l ^ 2) := by
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (mul_pos hy0 (sq_pos_of_pos hl0)) hl0).mpr
    nlinarith only [hy, hl, mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hl)]
  have hd : 1 ≤ (1 + 1 / y) ^ 2 := by nlinarith only [hi]
  have ha0 : 0 ≤ (1 / l - 2 / (y * l ^ 2)) / (1 + 1 / y) ^ 2 := div_nonneg hc (sq_nonneg _)
  have ha : (1 / l - 2 / (y * l ^ 2)) / (1 + 1 / y) ^ 2 ≤ 1 / l - 2 / (y * l ^ 2) := by
    simpa only [div_one] using div_le_div_of_nonneg_left hc (by norm_num only : (0 : ℝ) < 1) hd
  have hm := mul_le_mul_of_nonneg_right (neg_le_neg hE) ha0
  have hm' := mul_le_mul_of_nonneg_left ha hC0
  have hCy : 1 ≤ C * y := by
    nlinarith only [hy, hC, mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hy)]
  have hr : C * (1 / l - 2 / (y * l ^ 2)) - C / l + 2 / (y ^ 2 * l ^ 2) ≤ 0 := by
    field_simp [ne_of_gt hy0, ne_of_gt hl0]
    nlinarith only [hCy]
  linarith only [hm, hm', hr]

/-- For y >= 10 and l >= 2, the lower coefficient is at most 110/(81l),
and its difference from 1/l is at least 2/(y l). Bound the squared
denominator below by 81/100 and use y l >= 20. These two estimates
separate the parity-dependent remainder from the cancellation gain. -/
private theorem lower_parity_coefficient_bounds (y l : ℝ) (hy : 10 ≤ y) (hl : 2 ≤ l) :
    ((1 / l + 2 / (y * l ^ 2)) / (1 - 1 / y) ^ 2) ≤ 110 / (81 * l) ∧
      2 / (y * l) ≤ ((1 / l + 2 / (y * l ^ 2)) / (1 - 1 / y) ^ 2) - 1 / l := by
  have hy0 : 0 < y := by linarith only [hy]
  have hl0 : 0 < l := by linarith only [hl]
  have hi : 0 ≤ 1 / y := div_nonneg (by norm_num only) hy0.le
  have hib : 1 / y ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num only) hy
  have hd : 81 / 100 ≤ (1 - 1 / y) ^ 2 := by nlinarith only [hi, hib]
  have hd0 : 0 < (1 - 1 / y) ^ 2 := lt_of_lt_of_le (by norm_num only) hd
  have hc : 1 / l + 2 / (y * l ^ 2) ≤ 11 / (10 * l) := by
    field_simp [ne_of_gt hy0, ne_of_gt hl0]
    nlinarith only [hy, hl, mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hl)]
  constructor
  · have h :=
      (div_le_div_of_nonneg_right hc hd0.le).trans
        (div_le_div_of_nonneg_left
          (div_nonneg (by norm_num only) (mul_nonneg (by norm_num only) hl0.le))
          (by norm_num only : (0 : ℝ) < 81 / 100) hd)
    convert h using 1
    field_simp [ne_of_gt hl0]
    norm_num only
  · have hm : (1 / l) / (1 - 1 / y) ^ 2 ≤ (1 / l + 2 / (y * l ^ 2)) / (1 - 1 / y) ^ 2 :=
      div_le_div_of_nonneg_right
        (le_add_of_nonneg_right (div_nonneg (by norm_num only) (mul_nonneg hy0.le (sq_nonneg _))))
        hd0.le
    have hb : 2 / (y * l) ≤ (1 / l) / (1 - 1 / y) ^ 2 - 1 / l := by
      have hym : y - 1 ≠ 0 := ne_of_gt (by linarith only [hy] : 0 < y - 1)
      field_simp [ne_of_gt hy0, ne_of_gt hl0, hym]
      apply (le_div_iff₀ (sq_pos_of_ne_zero hym)).mpr
      nlinarith only [hy]
    linarith only [hm, hb]

/-- For y ≥ 10, 2 ≤ l ≤ 3y/5, C ≥ 9/10 and E ≤ -C+(l+4/3)/y²,
the lower parity combination is nonnegative. Bound the gain below by 3/y^2,
the remainder above by 550/(243y^2), and the error above by 1/(2y^2). -/
private theorem lower_even_parity_cancellation (y l C E : ℝ) (hy : 10 ≤ y) (hl : 2 ≤ l)
    (hly : l ≤ 3 * y / 5) (hC : 9 / 10 ≤ C) (hE : E ≤ -C + (l + 4 / 3) / y ^ 2) :
    0 ≤ -E * ((1 / l + 2 / (y * l ^ 2)) / (1 - 1 / y) ^ 2) - C / l - 2 / (y ^ 2 * l ^ 2) := by
  let A := (1 / l + 2 / (y * l ^ 2)) / (1 - 1 / y) ^ 2
  have hy0 : 0 < y := by linarith only [hy]
  have hl0 : 0 < l := by linarith only [hl]
  have hA := lower_parity_coefficient_bounds y l hy hl
  have hA0 : 0 ≤ A :=
    div_nonneg
      (add_nonneg (div_nonneg (by norm_num only) hl0.le)
        (div_nonneg (by norm_num only) (mul_nonneg hy0.le (sq_nonneg _))))
      (sq_nonneg _)
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hb0 : 0 ≤ A - 1 / l := (div_nonneg (by norm_num only) (mul_nonneg hy0.le hl0.le)).trans hA.2
  have hgain : 3 / y ^ 2 ≤ C * (A - 1 / l) := by
    have hm := mul_le_mul hC hA.2 (div_nonneg (by norm_num only) (mul_nonneg hy0.le hl0.le)) hC0
    have hr : 3 / y ^ 2 ≤ (9 / 10) * (2 / (y * l)) := by
      field_simp [ne_of_gt hy0, ne_of_gt hl0]
      linarith only [hly]
    exact hr.trans hm
  have hdelta : 0 ≤ (l + 4 / 3) / y ^ 2 := div_nonneg (by linarith only [hl]) (sq_nonneg _)
  have hloss : (E + C) * A ≤ 550 / (243 * y ^ 2) := by
    have hm :=
      mul_le_mul_of_nonneg_right (show E + C ≤ (l + 4 / 3) / y ^ 2 by linarith only [hE]) hA0
    have hm' := mul_le_mul_of_nonneg_left hA.1 hdelta
    have hr : ((l + 4 / 3) / y ^ 2) * (110 / (81 * l)) ≤ 550 / (243 * y ^ 2) := by
      field_simp [ne_of_gt hy0, ne_of_gt hl0]
      linarith only [hl]
    exact hm.trans (hm'.trans hr)
  have herr : 2 / (y ^ 2 * l ^ 2) ≤ 1 / (2 * y ^ 2) := by
    apply
      (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hy0) (sq_pos_of_pos hl0))
          (mul_pos (by norm_num only) (sq_pos_of_pos hy0))).mpr
    nlinarith only [hl, mul_nonneg (sq_nonneg y) (show 0 ≤ l ^ 2 - 4 by nlinarith only [hl])]
  have hr : 0 ≤ 3 / y ^ 2 - 550 / (243 * y ^ 2) - 1 / (2 * y ^ 2) := by
    field_simp [ne_of_gt hy0]
    norm_num only [zero_mul]
  change 0 ≤ -E * A - C / l - 2 / (y ^ 2 * l ^ 2)
  have hid :
    -E * A - C / l - 2 / (y ^ 2 * l ^ 2) = C * (A - 1 / l) - (E + C) * A - 2 / (y ^ 2 * l ^ 2) := by
    ring
  rw [hid]
  linarith only [hgain, hloss, herr, hr]

/-- For y ≥ 10, l ≥ 2, C ≥ 1/4 and E+C ≤ 11/(10y²), the lower
parity combination is nonnegative. The gain 1/(2yl) dominates the remainder
121/(81y^2 l) and the residual error 1/(y^2 l) for y >= 10. -/
private theorem lower_odd_parity_cancellation (y l C E : ℝ) (hy : 10 ≤ y) (hl : 2 ≤ l)
    (hC : 1 / 4 ≤ C) (hE : E ≤ -C + 11 / (10 * y ^ 2)) :
    0 ≤ -E * ((1 / l + 2 / (y * l ^ 2)) / (1 - 1 / y) ^ 2) - C / l - 2 / (y ^ 2 * l ^ 2) := by
  let A := (1 / l + 2 / (y * l ^ 2)) / (1 - 1 / y) ^ 2
  have hy0 : 0 < y := by linarith only [hy]
  have hl0 : 0 < l := by linarith only [hl]
  have hA := lower_parity_coefficient_bounds y l hy hl
  have hA0 : 0 ≤ A :=
    div_nonneg
      (add_nonneg (div_nonneg (by norm_num only) hl0.le)
        (div_nonneg (by norm_num only) (mul_nonneg hy0.le (sq_nonneg _))))
      (sq_nonneg _)
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hgain : 1 / (2 * y * l) ≤ C * (A - 1 / l) := by
    have hm := mul_le_mul hC hA.2 (div_nonneg (by norm_num only) (mul_nonneg hy0.le hl0.le)) hC0
    convert hm using 1
    field_simp [ne_of_gt hy0, ne_of_gt hl0]
    norm_num only
  have hloss : (E + C) * A ≤ 121 / (81 * y ^ 2 * l) := by
    have hm := mul_le_mul_of_nonneg_right (show E + C ≤ 11 / (10 * y ^ 2) by linarith only [hE]) hA0
    have hdelta : 0 ≤ 11 / (10 * y ^ 2) :=
      div_nonneg (by norm_num only) (mul_nonneg (by norm_num only) (sq_nonneg y))
    have hm' := mul_le_mul_of_nonneg_left hA.1 hdelta
    apply hm.trans (hm'.trans_eq ?_)
    field_simp [ne_of_gt hy0, ne_of_gt hl0]
    norm_num only
  have herr : 2 / (y ^ 2 * l ^ 2) ≤ 1 / (y ^ 2 * l) := by
    apply
      (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hy0) (sq_pos_of_pos hl0))
          (mul_pos (sq_pos_of_pos hy0) hl0)).mpr
    have h := mul_nonneg (mul_nonneg (sq_nonneg y) hl0.le) (sub_nonneg.mpr hl)
    nlinarith only [h]
  have hr : 0 ≤ 1 / (2 * y * l) - 121 / (81 * y ^ 2 * l) - 1 / (y ^ 2 * l) := by
    field_simp [ne_of_gt hy0, ne_of_gt hl0]
    linarith only [hy]
  change 0 ≤ -E * A - C / l - 2 / (y ^ 2 * l ^ 2)
  have hid :
    -E * A - C / l - 2 / (y ^ 2 * l ^ 2) = C * (A - 1 / l) - (E + C) * A - 2 / (y ^ 2 * l ^ 2) := by
    ring
  rw [hid]
  linarith only [hgain, hloss, herr, hr]

/-- For x >= 100, the reciprocal parity correction, gamma constant and
upper bounded error have a nonpositive combined contribution. Apply the
correction lower bounds separately to even and odd characters and use the
nonnegative upper zero-mass coefficient. This removes parity from the upper
L-value estimate. -/
theorem reciprocalCorrection_upper_cancellation {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 100 ≤ x) :
    -reciprocalCorrection χ x *
            ((1 / Real.log x - 2 / (Real.sqrt x * (Real.log x) ^ 2)) / (1 + 1 / Real.sqrt x) ^ 2) -
          (if χ (-1) = 1 then Real.log 2 + Real.eulerMascheroniConstant / 2
            else Real.eulerMascheroniConstant / 2) /
            Real.log x +
        2 / (x * (Real.log x) ^ 2) ≤
      0 := by
  have hb := sqrt_log_cutoff_bounds x hx
  have hx0 : 0 ≤ x := le_trans (by norm_num only : (0 : ℝ) ≤ 100) hx
  by_cases he : χ (-1) = 1
  · have hC : 1 / 4 ≤ Real.log 2 + Real.eulerMascheroniConstant / 2 := by
      linarith only [Real.log_two_gt_d9, Real.one_half_lt_eulerMascheroniConstant]
    have h :=
      upper_parity_cancellation (Real.sqrt x) (Real.log x)
        (Real.log 2 + Real.eulerMascheroniConstant / 2) (reciprocalCorrectionEven x) hb.1 hb.2.1 hC
        (by
          have hE := (reciprocalCorrectionEven_bounds x hx).1
          linarith only [hE])
    simpa only [reciprocalCorrection, ite_eq_left he, Real.sq_sqrt hx0] using h
  · have hC : 1 / 4 ≤ Real.eulerMascheroniConstant / 2 := by
      linarith only [Real.one_half_lt_eulerMascheroniConstant]
    have h :=
      upper_parity_cancellation (Real.sqrt x) (Real.log x) (Real.eulerMascheroniConstant / 2)
        (reciprocalCorrectionOdd x) hb.1 hb.2.1 hC
        (by simpa only [neg_div] using (reciprocalCorrectionOdd_bounds x hx).1)
    simpa only [reciprocalCorrection, ite_eq_right he, Real.sq_sqrt hx0] using h

/-- For x >= 100, the reciprocal parity correction, gamma constant and
lower bounded error have a nonnegative combined contribution. Apply the
different remainder bounds for even and odd characters, using the lower
coefficient bounds and log x <= 3 sqrt x/5. This removes parity from the
lower L-value estimate. -/
theorem reciprocalCorrection_lower_cancellation {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 100 ≤ x) :
    0 ≤
      -reciprocalCorrection χ x *
          ((1 / Real.log x + 2 / (Real.sqrt x * (Real.log x) ^ 2)) / (1 - 1 / Real.sqrt x) ^ 2) -
        (if χ (-1) = 1 then Real.log 2 + Real.eulerMascheroniConstant / 2
          else Real.eulerMascheroniConstant / 2) /
          Real.log x -
        2 / (x * (Real.log x) ^ 2) := by
  have hb := sqrt_log_cutoff_bounds x hx
  have hx0 : 0 ≤ x := le_trans (by norm_num only : (0 : ℝ) ≤ 100) hx
  by_cases he : χ (-1) = 1
  · have hC : 9 / 10 ≤ Real.log 2 + Real.eulerMascheroniConstant / 2 := by
      linarith only [Real.log_two_gt_d9, Real.one_half_lt_eulerMascheroniConstant]
    have hE :
      reciprocalCorrectionEven x ≤
        -(Real.log 2 + Real.eulerMascheroniConstant / 2) +
          (Real.log x + 4 / 3) / (Real.sqrt x) ^ 2 := by
      rw [Real.sq_sqrt hx0]
      have hd :=
        div_le_div_of_nonneg_right
          (show Real.log x + 1 + Real.eulerMascheroniConstant / 2 ≤ Real.log x + 4 / 3 by
            linarith only [Real.eulerMascheroniConstant_lt_two_thirds])
          hx0
      have h := (reciprocalCorrectionEven_bounds x hx).2
      linarith only [h, hd]
    have h :=
      lower_even_parity_cancellation (Real.sqrt x) (Real.log x)
        (Real.log 2 + Real.eulerMascheroniConstant / 2) (reciprocalCorrectionEven x) hb.1 hb.2.1
        hb.2.2 hC hE
    simpa only [reciprocalCorrection, ite_eq_left he, Real.sq_sqrt hx0] using h
  · have hC : 1 / 4 ≤ Real.eulerMascheroniConstant / 2 := by
      linarith only [Real.one_half_lt_eulerMascheroniConstant]
    have hE :
      reciprocalCorrectionOdd x ≤
        -(Real.eulerMascheroniConstant / 2) + 11 / (10 * (Real.sqrt x) ^ 2) := by
      rw [Real.sq_sqrt hx0]
      have hd :=
        div_le_div_of_nonneg_right
          (show Real.log 2 + Real.eulerMascheroniConstant / 2 ≤ 11 / 10 by
            linarith only [Real.log_two_lt_d9, Real.eulerMascheroniConstant_lt_two_thirds])
          hx0
      have h := (reciprocalCorrectionOdd_bounds x hx).2
      have heq : (11 / 10) / x = 11 / (10 * x) := by ring
      rw [heq] at hd
      linarith only [h, hd]
    have h :=
      lower_odd_parity_cancellation (Real.sqrt x) (Real.log x) (Real.eulerMascheroniConstant / 2)
        (reciprocalCorrectionOdd x) hb.1 hb.2.1 hC hE
    simpa only [reciprocalCorrection, ite_eq_right he, Real.sq_sqrt hx0] using h

/-- At cutoff at least 100, an even complex character has the even reciprocal
correction upper bound, retaining the negative logarithm of two and gamma terms.
Select the even branch and use its existing tail estimate.
This supplies a parity-dependent bound for finite character averages. -/
theorem reciprocalCorrection_le_even {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ.Even) {x : ℝ}
    (hx : 100 ≤ x) :
    reciprocalCorrection χ x ≤
      -Real.log 2 - Real.eulerMascheroniConstant / 2 +
        (Real.log x + 1 + Real.eulerMascheroniConstant / 2) / x := by
  change χ (-1) = 1 at hχ
  simpa only [reciprocalCorrection, ite_eq_left hχ] using (reciprocalCorrectionEven_bounds x hx).2

/-- At cutoff at least 100, an odd complex character has the odd reciprocal
correction upper bound, retaining the negative gamma term.
Oddness excludes the even branch, so apply the existing odd tail estimate.
This supplies the second parity branch in finite character averages. -/
theorem reciprocalCorrection_le_odd {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) {x : ℝ}
    (hx : 100 ≤ x) :
    reciprocalCorrection χ x ≤
      -Real.eulerMascheroniConstant / 2 + (Real.log 2 + Real.eulerMascheroniConstant / 2) / x := by
  have h : χ (-1) ≠ 1 := hχ.not_even
  simpa only [reciprocalCorrection, ite_eq_right h] using (reciprocalCorrectionOdd_bounds x hx).2

end PseudoPrime.LLS.PaperStatements
