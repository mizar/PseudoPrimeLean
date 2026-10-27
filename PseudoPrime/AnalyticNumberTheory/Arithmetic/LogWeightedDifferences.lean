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

/-- A nonnegative square-root smoothing constant C and the corresponding endpoint
bounds imply error at most (1+6C)s³ at cutoff s⁴ for s≥2. Compare the two cubic-step
intervals with the cutoff, and bound their square roots by the quadratic scale. -/
private theorem psi_error_fourth_power_of_short_interval_bounds {C : ℝ} (hC : 0 ≤ C)
    (hb :
      ∀ {x y : ℝ},
        1 < x →
          x < y →
          Chebyshev.psi x ≤ y + C * (Real.sqrt x + Real.sqrt y) * y / (y - x) ∧
            x - C * (Real.sqrt x + Real.sqrt y) * x / (y - x) ≤ Chebyshev.psi y)
    {s : ℝ} (hs : 2 ≤ s) : |Chebyshev.psi (s ^ 4) - s ^ 4| ≤ (1 + 6 * C) * s ^ 3 := by
  have hs0 : 0 < s := (by norm_num only : (0 : ℝ) < 2).trans_le hs
  have hs1 : 1 ≤ s := (by norm_num only : (1 : ℝ) ≤ 2).trans hs
  have hp3 : 0 < s ^ 3 := pow_pos hs0 _
  have hp2 : 0 ≤ s ^ 2 := sq_nonneg s
  have h23 : s ^ 2 ≤ s ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hs1 hp2
    nlinarith only [h]
  have hs3 : 8 ≤ s ^ 3 := by
    simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num only] using
      pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 2) hs 3
  have hx : 1 < s ^ 4 := by nlinarith only [hs3, h23, hs]
  have ha : 1 < s ^ 4 - s ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hs hp3.le
    nlinarith only [h, hs3]
  have hroot : Real.sqrt (s ^ 4) = s ^ 2 := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sqrt_sq hp2]
  have hrootU : Real.sqrt (s ^ 4 + s ^ 3) ≤ 2 * s ^ 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith only [hp2]
    · have h := mul_le_mul_of_nonneg_left hs1 hp3.le
      nlinarith only [h, sq_nonneg (s ^ 2)]
  have hrootL : Real.sqrt (s ^ 4 - s ^ 3) ≤ s ^ 2 := by
    rw [← hroot]
    exact Real.sqrt_le_sqrt (sub_le_self _ hp3.le)
  have hu := (hb hx (show s ^ 4 < s ^ 4 + s ^ 3 by linarith only [hp3])).1
  have hl := (hb ha (show s ^ 4 - s ^ 3 < s ^ 4 by linarith only [hp3])).2
  rw [hroot, add_sub_cancel_left] at hu
  rw [hroot, sub_sub_cancel] at hl
  have huB :
    C * (s ^ 2 + Real.sqrt (s ^ 4 + s ^ 3)) * (s ^ 4 + s ^ 3) / s ^ 3 ≤
      C * (3 * s ^ 2) * (s ^ 4 + s ^ 3) / s ^ 3 := by
    apply div_le_div_of_nonneg_right _ hp3.le
    apply mul_le_mul_of_nonneg_right _ (by nlinarith only [hx, hp3])
    exact mul_le_mul_of_nonneg_left (by linarith only [hrootU]) hC
  have hlB :
    C * (Real.sqrt (s ^ 4 - s ^ 3) + s ^ 2) * (s ^ 4 - s ^ 3) / s ^ 3 ≤
      C * (2 * s ^ 2) * (s ^ 4 - s ^ 3) / s ^ 3 := by
    apply div_le_div_of_nonneg_right _ hp3.le
    apply mul_le_mul_of_nonneg_right _ (by linarith only [ha])
    exact mul_le_mul_of_nonneg_left (by linarith only [hrootL]) hC
  have heU : C * (3 * s ^ 2) * (s ^ 4 + s ^ 3) / s ^ 3 = 3 * C * (s ^ 3 + s ^ 2) := by
    apply (div_eq_iff (pow_ne_zero 3 hs0.ne')).mpr
    ring
  have heL : C * (2 * s ^ 2) * (s ^ 4 - s ^ 3) / s ^ 3 = 2 * C * (s ^ 3 - s ^ 2) := by
    apply (div_eq_iff (pow_ne_zero 3 hs0.ne')).mpr
    ring
  rw [heU] at huB
  rw [heL] at hlB
  have hC23 := mul_le_mul_of_nonneg_left h23 hC
  have hC2 := mul_nonneg hC hp2
  have hC3 := mul_nonneg hC hp3.le
  rw [abs_le]
  constructor <;> nlinarith only [hu, hl, huB, hlB, hC23, hC2, hC3]

/-- If the logarithmically smoothed Mangoldt sum has error at most C sqrt(x) for
x>1, with C≥0, then psi has error at most (1+6C)sqrt(x)sqrt(sqrt(x)) for x≥16.
Finite differences at cubic steps supply the fourth-power bound; representing x by
its iterated square root gives the general cutoff. No RH hypothesis is used here. -/
theorem psi_error_le_three_quarter_of_logWeighted_error {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ {x : ℝ}, 1 < x → |logWeightedMangoldtSum x - x| ≤ C * Real.sqrt x) {x : ℝ}
    (hx : 16 ≤ x) :
    |Chebyshev.psi x - x| ≤ (1 + 6 * C) * Real.sqrt x * Real.sqrt (Real.sqrt x) := by
  have hb : ∀ {s : ℝ}, 2 ≤ s → |Chebyshev.psi (s ^ 4) - s ^ 4| ≤ (1 + 6 * C) * s ^ 3 := by
    apply psi_error_fourth_power_of_short_interval_bounds hC
    intro u v hu huv
    have h :=
      psi_bounds_of_logWeighted_error_without_log (zero_lt_one.trans hu) huv (hbound hu)
        (hbound (hu.trans huv))
    simpa only [← mul_add] using h
  have hx0 : 0 ≤ x := (by norm_num only : (0 : ℝ) ≤ 16).trans hx
  have hr : 4 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hx
    rw [show (16 : ℝ) = (4 : ℝ) ^ 2 by norm_num only, Real.sqrt_sq (by norm_num only)] at h
    exact h
  have hs : 2 ≤ Real.sqrt (Real.sqrt x) := by
    have h := Real.sqrt_le_sqrt hr
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num only, Real.sqrt_sq (by norm_num only)] at h
    exact h
  have hs2 := Real.sq_sqrt (Real.sqrt_nonneg x)
  have hx2 := Real.sq_sqrt hx0
  have he : Real.sqrt (Real.sqrt x) ^ 4 = x := by nlinarith only [hs2, hx2]
  have h := hb hs
  rw [he] at h
  have hm :
    (1 + 6 * C) * Real.sqrt x * Real.sqrt (Real.sqrt x) =
      (1 + 6 * C) * Real.sqrt (Real.sqrt x) ^ 3 := by
    calc
      _ = (1 + 6 * C) * Real.sqrt (Real.sqrt x) ^ 2 * Real.sqrt (Real.sqrt x) :=
        congrArg (fun z ↦ (1 + 6 * C) * z * Real.sqrt (Real.sqrt x)) hs2.symm
      _ = _ := by ring
  rw [hm]
  exact h

end PseudoPrime.AnalyticNumberTheory.Arithmetic
