/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperDefinitions
public import PseudoPrime.Analysis.NumericalLogBounds
public import PseudoPrime.Analysis.EulerMascheroniBounds
public import Mathlib.Tactic

/-! # Bounds for the parity corrections in logarithmic character sums

Geometric majorants control the even and odd tails. Their constants absorb
these tails, leaving explicit logarithmic bounds for the coset comparison.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For cutoff at least `100` and natural parity shift `a`, the logarithmic
tail with exponent and denominator `2k+1+a` is nonnegative and at most `1/4`.
Its terms are bounded by the geometric series starting at `1/x`.
This controls both parity tails below their positive pi-squared constants. -/
theorem logParityTail_bounds {x : ℝ} (hx : 100 ≤ x) (a : ℕ) :
    0 ≤ (∑' k : ℕ, 1 / (x ^ (2 * k + 1 + a) * (2 * (k : ℝ) + 1 + a) ^ 2)) ∧
      (∑' k : ℕ, 1 / (x ^ (2 * k + 1 + a) * (2 * (k : ℝ) + 1 + a) ^ 2)) ≤ (1 / 4 : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hx1 : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ 100).trans hx
  have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
  have hr : x⁻¹ < 1 := (inv_lt_one₀ hx0).mpr (lt_of_lt_of_le (by norm_num only) hx)
  have hg := (summable_geometric_of_lt_one hi hr).mul_left x⁻¹
  have hn (k : ℕ) : 0 ≤ 1 / (x ^ (2 * k + 1 + a) * (2 * (k : ℝ) + 1 + a) ^ 2) :=
    div_nonneg zero_le_one (mul_nonneg (pow_nonneg hx0.le _) (sq_nonneg _))
  have hb (k : ℕ) : 1 / (x ^ (2 * k + 1 + a) * (2 * (k : ℝ) + 1 + a) ^ 2) ≤ x⁻¹ * (x⁻¹) ^ k := by
    have he : k + 1 ≤ 2 * k + 1 + a := by
      rw [two_mul]
      exact (Nat.add_le_add_right (Nat.le_add_left k k) 1).trans (Nat.le_add_right (k + k + 1) a)
    have hd : 1 ≤ (2 * (k : ℝ) + 1 + a) ^ 2 := by
      nlinarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
    have hm := mul_le_mul_of_nonneg_left hd (pow_nonneg hx0.le (2 * k + 1 + a))
    have hpow := pow_le_pow_right₀ hx1 he
    have ht : 1 / (x ^ (2 * k + 1 + a) * (2 * (k : ℝ) + 1 + a) ^ 2) ≤ 1 / x ^ (k + 1) :=
      one_div_le_one_div_of_le (pow_pos hx0 _) (hpow.trans (by simpa only [mul_one] using hm))
    apply ht.trans_eq
    simp only [one_div, pow_succ, mul_inv_rev, inv_pow]
  have hs := hg.of_nonneg_of_le hn hb
  constructor
  · exact tsum_nonneg hn
  · have hbound := hs.tsum_le_tsum hb hg
    rw [tsum_mul_left, tsum_geometric_of_lt_one hi hr] at hbound
    have hlast : x⁻¹ * (1 - x⁻¹)⁻¹ ≤ (1 / 4 : ℝ) := by
      have hi100 : x⁻¹ ≤ (1 / 100 : ℝ) := by
        simpa only [one_div] using (inv_le_inv₀ hx0 (by norm_num only : (0 : ℝ) < 100)).mpr hx
      apply (mul_inv_le_iff₀ (sub_pos.mpr hr)).mpr
      linarith only [hi100]
    exact hbound.trans hlast

/-- A cutoff at least `100` has logarithm at least four. Compare with `81`
and use the certified lower bound for `log 3`. This fixes signs in the parity
correction estimates. -/
private theorem four_le_log_of_hundred {x : ℝ} (hx : 100 ≤ x) : (4 : ℝ) ≤ Real.log x := by
  have h :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 81) ((by norm_num only : (81 : ℝ) ≤ 100).trans hx)
  rw [show (81 : ℝ) = 3 ^ (4 : ℕ) by norm_num only, Real.log_pow] at h
  norm_num only at h
  linarith only [h, Real.log_three_gt_d9]

/-- At cutoff at least `100`, the even correction lies between
`-gamma log x/2 - log² x/2` and zero. The geometric tail is below the positive
pi-squared constant, and the logarithmic terms dominate that constant.
This controls the even branch of the coset norm estimate. -/
theorem logCorrectionEven_bounds {x : ℝ} (hx : 100 ≤ x) :
    -Real.eulerMascheroniConstant / 2 * Real.log x - (Real.log x) ^ 2 / 2 ≤ logCorrectionEven x ∧
      logCorrectionEven x ≤ 0 := by
  have ht := logParityTail_bounds hx 1
  have he :
    (∑' k : ℕ, 1 / (x ^ (2 * k + 1 + 1) * (2 * (k : ℝ) + 1 + 1) ^ 2)) =
      ∑' k : ℕ, 1 / (x ^ (2 * (k + 1)) * (2 * ((k : ℝ) + 1)) ^ 2) := by
    apply tsum_congr
    intro k
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
      show 2 * (k : ℝ) + 1 + 1 = 2 * ((k : ℝ) + 1) by ring]
  norm_num only [Nat.cast_one] at ht
  rw [he] at ht
  have hl := four_le_log_of_hundred hx
  rw [logCorrectionEven]
  constructor <;>
    nlinarith only [ht.1, ht.2, hl, Real.pi_gt_three, Real.pi_lt_four,
      Real.one_half_lt_eulerMascheroniConstant]

/-- At cutoff at least `100`, the odd correction lies between
`-(log 2 + gamma/2) log x` and zero. The geometric tail is below the positive
pi-squared constant, and the logarithmic term dominates that constant.
This controls the odd branch of the coset norm estimate. -/
theorem logCorrectionOdd_bounds {x : ℝ} (hx : 100 ≤ x) :
    -(Real.log 2 + Real.eulerMascheroniConstant / 2) * Real.log x ≤ logCorrectionOdd x ∧
      logCorrectionOdd x ≤ 0 := by
  have ht := logParityTail_bounds hx 0
  simp only [Nat.cast_zero, add_zero] at ht
  have hl := four_le_log_of_hundred hx
  rw [logCorrectionOdd]
  constructor <;>
    nlinarith only [ht.1, ht.2, hl, Real.pi_gt_three, Real.pi_lt_four,
      Real.one_half_lt_eulerMascheroniConstant, Real.log_two_gt_d9]

end PseudoPrime.LLS.PaperStatements
