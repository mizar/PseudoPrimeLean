/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RiemannWeightedUpperBounds

/-! # Root cutoff comparisons for composite prime-power sums

Normalize real root terms by the square root of the cutoff. Their ratios
decrease above a fixed positive base, allowing finite rational certificates.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Above a positive base `b`, the ratio `x^r/sqrt x` decreases when `r ≤ 1/2`.
Rewrite the ratio as the power with exponent `r-1/2` and use antitonicity
of nonpositive powers. This transfers root cutoff bounds to a fixed base. -/
theorem root_div_sqrt_le_at_base {b x r : ℝ} (hb : 0 < b) (hx : b ≤ x) (hr : r ≤ 1 / 2) :
    x ^ r / Real.sqrt x ≤ b ^ r / Real.sqrt b := by
  have h := Real.rpow_le_rpow_of_nonpos hb hx (sub_nonpos.mpr hr)
  rw [Real.rpow_sub (hb.trans_le hx), Real.rpow_sub hb] at h
  simpa only [Real.sqrt_eq_rpow] using h

/-- If `b ≤ N^k` for a nonnegative real `N` and positive natural `k`, its
real `k`th root is at most `N`. Raise the inequality to the reciprocal exponent
and cancel the positive integer exponent. This permits exact rational root
certificates for the finitely many small prime-power exponents. -/
theorem root_le_of_le_nat_pow {b N : ℝ} (hb : 0 ≤ b) (hN : 0 ≤ N) {k : ℕ} (hk : 0 < k)
    (hbound : b ≤ N ^ k) : b ^ ((1 : ℝ) / k) ≤ N := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := Real.rpow_le_rpow hb hbound (div_nonneg zero_le_one hk0.le)
  rw [← Real.rpow_natCast N k, ← Real.rpow_mul hN, mul_one_div_cancel hk0.ne', Real.rpow_one] at h
  exact h

/-- Above a positive base, each exponent-`k` root slice with `k≥2`,
normalized by the cutoff square root, is at most its value at the base.
Apply the decreasing-power comparison to both the root and its square root.
This controls each term of the finite composite prime-power majorant. -/
theorem rootSlice_div_sqrt_le_at_base {b x : ℝ} (hb : 0 < b) (hx : b ≤ x) {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20) / Real.sqrt x ≤
      (k : ℝ) * (b ^ ((1 : ℝ) / k) + Real.sqrt (b ^ ((1 : ℝ) / k)) / 20) / Real.sqrt b := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (by norm_num only) hk2
  have hr : (1 : ℝ) / k ≤ 1 / 2 := (div_le_iff₀ hk0).mpr (by linarith only [hk2])
  have hr2 : ((1 : ℝ) / k) / 2 ≤ 1 / 2 := by linarith only [hr]
  have h1 := root_div_sqrt_le_at_base hb hx hr
  have h2 := root_div_sqrt_le_at_base hb hx hr2
  have he (y : ℝ) (hy : 0 ≤ y) : Real.sqrt (y ^ ((1 : ℝ) / k)) = y ^ (((1 : ℝ) / k) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy]
    congr 1
    ring
  rw [he x (hb.trans_le hx).le, he b hb.le]
  have h1m := mul_le_mul_of_nonneg_left h1 hk0.le
  have h2m := mul_le_mul_of_nonneg_left h2 hk0.le
  simp only [div_eq_mul_inv] at h1m h2m ⊢
  nlinarith only [h1m, h2m]

/-- For any fixed exponent endpoint `n`, the root majorant over exponents
from two through `n`, divided by the cutoff square root, decreases above a
positive base. Sum the termwise normalized comparisons.
This reduces every fixed finite prefix to a certificate at one base. -/
theorem rootPrefix_div_sqrt_le_at_base {b x : ℝ} (hb : 0 < b) (hx : b ≤ x) (n : ℕ) :
    (∑ k ∈ Finset.Icc 2 n, (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) /
        Real.sqrt x ≤
      (∑ k ∈ Finset.Icc 2 n, (k : ℝ) * (b ^ ((1 : ℝ) / k) + Real.sqrt (b ^ ((1 : ℝ) / k)) / 20)) /
        Real.sqrt b := by
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_le_sum
  intro k hk
  exact rootSlice_div_sqrt_le_at_base hb hx (Finset.mem_Icc.mp hk).1

end PseudoPrime.LLS.PaperStatements
