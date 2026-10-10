/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt

/-! # Logarithmic finite differences and Chebyshev bounds

Positive Mangoldt coefficients transfer bounds for the logarithmically smoothed sum
to bounds for the unsmoothed Chebyshev function. No RH or prime number theorem is
assumed in the finite-sum comparisons.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For real cutoffs x <= y, pad the logarithmically weighted Mangoldt sum at x
with zero terms up to the floor of y. Terms above the original cutoff vanish by
the explicit indicator, and the positive interval at x is included in that at y.
This puts two cutoffs on a common finite index set for difference estimates. -/
theorem logWeightedMangoldtSum_eq_extended {x y : ℝ} (hxy : x ≤ y) :
    logWeightedMangoldtSum x =
      ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, if n ≤ ⌊x⌋₊ then logWeightedMangoldtTerm x n else 0 := by
  classical
  have hs :=
    Finset.sum_subset (Finset.Ioc_subset_Ioc (le_refl 0) (Nat.floor_mono hxy)) (f := fun n ↦
      if n ≤ ⌊x⌋₊ then logWeightedMangoldtTerm x n else 0)
      (fun n hnY hn ↦ ite_eq_right (fun h ↦ hn (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hnY).1, h⟩)))
  have he :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, if n ≤ ⌊x⌋₊ then logWeightedMangoldtTerm x n else 0) =
      logWeightedMangoldtSum x := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [ite_eq_left (Finset.mem_Ioc.mp hn).2]
  exact he.symm.trans hs

/-- For positive cutoffs x <= y and a positive integer n <= y, the difference
between the term at y and the cutoff-restricted term at x lies between the
restricted and unrestricted value Lambda(n) log(y/x). Below x the two logarithms
subtract exactly; above x use positivity and monotonicity of log. Summing this
comparison recovers upper and lower Chebyshev bounds without a prime number theorem. -/
theorem logWeightedMangoldtTerm_difference {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) {n : ℕ} (hn : 0 < n)
    (hny : (n : ℝ) ≤ y) :
    (if n ≤ ⌊x⌋₊ then ArithmeticFunction.vonMangoldt n * Real.log (y / x) else 0) ≤
        logWeightedMangoldtTerm y n - (if n ≤ ⌊x⌋₊ then logWeightedMangoldtTerm x n else 0) ∧
      logWeightedMangoldtTerm y n - (if n ≤ ⌊x⌋₊ then logWeightedMangoldtTerm x n else 0) ≤
        ArithmeticFunction.vonMangoldt n * Real.log (y / x) := by
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hyp : 0 < y := hx.trans_le hxy
  by_cases hnX : n ≤ ⌊x⌋₊
  · rw [ite_eq_left hnX, ite_eq_left hnX]
    have he :
      logWeightedMangoldtTerm y n - logWeightedMangoldtTerm x n =
        ArithmeticFunction.vonMangoldt n * Real.log (y / x) := by
      rw [logWeightedMangoldtTerm, logWeightedMangoldtTerm, Real.log_div hyp.ne' hnp.ne',
        Real.log_div hx.ne' hnp.ne', Real.log_div hyp.ne' hx.ne']
      ring
    exact ⟨he.ge, he.le⟩
  · rw [ite_eq_right hnX, ite_eq_right hnX, sub_zero, logWeightedMangoldtTerm]
    have hxn : x ≤ (n : ℝ) := (lt_of_not_ge (fun h ↦ hnX ((Nat.le_floor_iff hx.le).mpr h))).le
    have hnlog := Real.log_nonneg ((le_div_iff₀ hnp).mpr (by simpa only [one_mul] using hny))
    have hlog : Real.log (y / (n : ℝ)) ≤ Real.log (y / x) := by
      rw [Real.log_div hyp.ne' hnp.ne', Real.log_div hyp.ne' hx.ne']
      exact sub_le_sub_left (Real.log_le_log hx hxn) _
    exact
      ⟨mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hnlog,
        mul_le_mul_of_nonneg_left hlog ArithmeticFunction.vonMangoldt_nonneg⟩

/-- For every real cutoff, Chebyshev psi is the sum of von Mangoldt over positive
indices through its natural floor. Remove the zero index, whose Mangoldt value is
zero. This matches the index convention of logarithmically weighted sums. -/
theorem psi_eq_positive_sum (x : ℝ) :
    Chebyshev.psi x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
  rw [Chebyshev.psi_eq_sum_Icc, ← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _)]
  simp only [ArithmeticFunction.map_zero, add_zero]

/-- For 0 < x <= y, the difference of logarithmically weighted Mangoldt sums
lies between psi(x) log(y/x) and psi(y) log(y/x). Pad the lower cutoff with zero
terms and sum the pointwise logarithmic comparison. This elementary finite-sum
inequality transfers smoothed explicit-formula errors to unsmoothed partial sums. -/
theorem logWeightedMangoldtSum_difference_bounds {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Chebyshev.psi x * Real.log (y / x) ≤ logWeightedMangoldtSum y - logWeightedMangoldtSum x ∧
      logWeightedMangoldtSum y - logWeightedMangoldtSum x ≤ Chebyshev.psi y * Real.log (y / x) := by
  classical
  have he :
    (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
        if n ≤ ⌊x⌋₊ then ArithmeticFunction.vonMangoldt n * Real.log (y / x) else 0) =
      Chebyshev.psi x * Real.log (y / x) := by
    have hs :=
      Finset.sum_subset (Finset.Ioc_subset_Ioc (le_refl 0) (Nat.floor_mono hxy)) (f := fun n ↦
        if n ≤ ⌊x⌋₊ then ArithmeticFunction.vonMangoldt n * Real.log (y / x) else 0)
        (fun n hnY hn ↦
          ite_eq_right (fun h ↦ hn (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hnY).1, h⟩)))
    rw [← hs, psi_eq_positive_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    exact ite_eq_left (Finset.mem_Ioc.mp hn).2
  rw [logWeightedMangoldtSum_eq_extended hxy, logWeightedMangoldtSum, ← Finset.sum_sub_distrib]
  constructor
  · rw [← he]
    apply Finset.sum_le_sum
    intro n hn
    exact
      (logWeightedMangoldtTerm_difference hx hxy (Finset.mem_Ioc.mp hn).1
          ((Nat.le_floor_iff (hx.trans_le hxy).le).mp (Finset.mem_Ioc.mp hn).2)).1
  · rw [psi_eq_positive_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro n hn
    exact
      (logWeightedMangoldtTerm_difference hx hxy (Finset.mem_Ioc.mp hn).1
          ((Nat.le_floor_iff (hx.trans_le hxy).le).mp (Finset.mem_Ioc.mp hn).2)).2

/-- For 0 < x < y, suppose the logarithmically weighted sum differs from its
cutoff by at most Ex and Ey at the two endpoints. Then psi(x) and psi(y) satisfy
the displayed upper and lower bounds, with error Ex+Ey divided by log(y/x).
Combine the finite difference inequalities with the two absolute error bounds and
divide by the positive logarithm. This isolates the arithmetic step in RH-based
quantitative estimates for cutoff kernel sums. -/
theorem psi_bounds_of_logWeighted_error {x y Ex Ey : ℝ} (hx : 0 < x) (hxy : x < y)
    (hxE : |logWeightedMangoldtSum x - x| ≤ Ex) (hyE : |logWeightedMangoldtSum y - y| ≤ Ey) :
    Chebyshev.psi x ≤ (y - x + Ex + Ey) / Real.log (y / x) ∧
      (y - x - Ex - Ey) / Real.log (y / x) ≤ Chebyshev.psi y := by
  have hl : 0 < Real.log (y / x) :=
    Real.log_pos ((lt_div_iff₀ hx).mpr (by simpa only [one_mul] using hxy))
  have h := logWeightedMangoldtSum_difference_bounds hx hxy.le
  have hEx := abs_le.mp hxE
  have hEy := abs_le.mp hyE
  constructor
  · apply (le_div_iff₀ hl).mpr
    linarith only [h.1, hEx.1, hEy.2]
  · apply (div_le_iff₀ hl).mpr
    linarith only [h.2, hEx.2, hEy.1]

/-- Under absolute smoothed errors Ex and Ey at 0 < x < y, bound psi(x) from above
and psi(y) from below without a logarithm in the denominator. Compare log(y/x) with
(y-x)/y and (y-x)/x, multiply by the nonnegative Chebyshev values, and cancel the
positive interval length. This gives quantitative short-interval estimates ready
for choosing a power-sized difference step. -/
theorem psi_bounds_of_logWeighted_error_without_log {x y Ex Ey : ℝ} (hx : 0 < x) (hxy : x < y)
    (hxE : |logWeightedMangoldtSum x - x| ≤ Ex) (hyE : |logWeightedMangoldtSum y - y| ≤ Ey) :
    Chebyshev.psi x ≤ y + (Ex + Ey) * y / (y - x) ∧
      x - (Ex + Ey) * x / (y - x) ≤ Chebyshev.psi y := by
  have hy : 0 < y := hx.trans hxy
  have hd : 0 < y - x := sub_pos.mpr hxy
  have hlo : (y - x) / y ≤ Real.log (y / x) := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
    rw [inv_div, one_sub_div hy.ne'] at h
    exact h
  have hhi : Real.log (y / x) ≤ (y - x) / x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
    rw [div_sub_one hx.ne'] at h
    exact h
  have h := logWeightedMangoldtSum_difference_bounds hx hxy.le
  have hEx := abs_le.mp hxE
  have hEy := abs_le.mp hyE
  have hu := mul_le_mul_of_nonneg_left hlo (Chebyshev.psi_nonneg x)
  have hl := mul_le_mul_of_nonneg_left hhi (Chebyshev.psi_nonneg y)
  have hupper : Chebyshev.psi x * (y - x) / y ≤ y - x + Ex + Ey := by
    rw [mul_div_assoc]
    linarith only [hu, h.1, hEx.1, hEy.2]
  have hlower : y - x - Ex - Ey ≤ Chebyshev.psi y * (y - x) / x := by
    rw [mul_div_assoc]
    linarith only [hl, h.2, hEx.2, hEy.1]
  have hu' := (div_le_iff₀ hy).mp hupper
  have hl' := (le_div_iff₀ hx).mp hlower
  constructor
  · apply (mul_le_mul_iff_left₀ hd).mp
    calc
      Chebyshev.psi x * (y - x) ≤ (y - x + Ex + Ey) * y := hu'
      _ = (y + (Ex + Ey) * y / (y - x)) * (y - x) := by
        simp only [add_mul, div_mul_cancel₀ _ hd.ne']
        ring
  · apply (mul_le_mul_iff_left₀ hd).mp
    calc
      (x - (Ex + Ey) * x / (y - x)) * (y - x) = (y - x - Ex - Ey) * x := by
        simp only [sub_mul, div_mul_cancel₀ _ hd.ne']
        ring
      _ ≤ Chebyshev.psi y * (y - x) := hl'

/-- For ordered real cutoffs, the Mangoldt sum over the natural-floor interval
equals psi(y)-psi(x). Split the two positive finite intervals, whose overlap is
empty, and remove the zero index. This connects endpoint Chebyshev limits with
step-function weighted sums without analytic assumptions. -/
theorem mangoldt_interval_sum_eq_psi_sub {x y : ℝ} (hxy : x ≤ y) :
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ArithmeticFunction.vonMangoldt n) =
      Chebyshev.psi y - Chebyshev.psi x := by
  have hd : Disjoint (Finset.Ioc 0 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    exact (not_lt_of_ge (Finset.mem_Ioc.mp hn).2) (Finset.mem_Ioc.mp hm).1
  have he := Finset.sum_union (f := fun n ↦ ArithmeticFunction.vonMangoldt n) hd
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (Nat.floor_mono hxy), ← psi_eq_positive_sum, ←
    psi_eq_positive_sum] at he
  linarith only [he]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
