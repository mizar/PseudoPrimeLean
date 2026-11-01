/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtSecondOrder
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Reduction of the second-order Mangoldt estimate to identification of its constant. -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A second-order psi estimate makes its logarithmic error kernel integrable on
the whole half-line above two. Choose a sufficiently large cutoff, combine compact
integrability with the existing tail majorant, and join the two intervals.
This permits defining the limiting constant without an extra integrability hypothesis. -/
theorem integrable_psiLogErrorKernel (hψ : PsiSecondOrderBound) :
    MeasureTheory.IntegrableOn psiLogErrorKernel (Set.Ioi 2) := by
  obtain ⟨B, hB, hb⟩ := hψ
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hb
  obtain ⟨x, hx, hl, hxa⟩ :=
    ((Filter.eventually_ge_atTop (2 : ℝ)).and
        ((Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))).and
          (Filter.eventually_ge_atTop a))).exists
  have hi :=
    integrableOn_psiLogErrorKernel_Ioi_of_bound hB ((by norm_num only : (1 : ℝ) < 2).trans_le hx) hl
      (fun t ht ↦ ha t (hxa.trans ht))
  have hf := (integrableOn_psiLogErrorKernel_Icc x).mono_set Set.Ioc_subset_Icc_self
  rw [← Set.Ioc_union_Ioi_eq_Ioi hx]
  exact hf.union hi

/-- The constant obtained by partial summation of the logarithmic Mangoldt sum.
It is the explicit lower-end contribution plus the full psi-error integral.
Under a second-order psi bound this integral is genuine; identifying this constant
with Euler's constant is a separate arithmetic task, not part of this definition. -/
noncomputable def psiMertensConstant : ℝ :=
  (1 / Real.log 2 - Real.log (Real.log 2)) + ∫ t in Set.Ioi 2, psiLogErrorKernel t

/-- With a second-order psi estimate and cutoff at least two, the Mangoldt sum
minus log-log and its integral constant equals the psi boundary error minus its tail.
Split the convergent error integral at the cutoff and use finite partial summation.
This exact identity connects the finite sum to the quantitative tail estimate. -/
theorem mangoldtLogSum_error_eq_tail (hψ : PsiSecondOrderBound) {x : ℝ} (hx : 2 ≤ x) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)) -
        Real.log (Real.log x) -
        psiMertensConstant =
      (Chebyshev.psi x - x) / (x * Real.log x) - ∫ t in Set.Ioi x, psiLogErrorKernel t := by
  have hi := intervalIntegral.integral_Ioi_sub_Ioi (integrable_psiLogErrorKernel hψ) hx
  rw [intervalIntegral.integral_of_le hx] at hi
  rw [mangoldtLogSum_sub_logLog_eq_psi_error hx]
  change _ + _ + (∫ t in Set.Ioc 2 x, psiLogErrorKernel t) - psiMertensConstant = _
  rw [← hi]
  dsimp only [psiMertensConstant]
  ring

/-- A second-order psi bound controls the Mangoldt error relative to its integral constant.
The conclusion provides a nonnegative constant and an eventual inverse-log-square bound.
Bound the psi boundary and the tail separately; no Euler-constant identification is used.
This supplies quantitative convergence before the value of the limit is known. -/
theorem mangoldtLogSum_error_bound (hψ : PsiSecondOrderBound) :
    ∃ A : ℝ,
      0 ≤ A ∧
        ∀ᶠ x : ℝ in Filter.atTop,
          |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)) -
                (Real.log (Real.log x) + psiMertensConstant)| ≤
            A / (Real.log x) ^ 2 := by
  obtain ⟨B, hB, hb⟩ := hψ
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hb
  refine ⟨2 * B, mul_nonneg (by norm_num only) hB, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop a, Filter.eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))] with x hxa hx hl
  have hx0 : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  have hl0 : 0 < Real.log x := zero_lt_one.trans_le hl
  have hboundary : |(Chebyshev.psi x - x) / (x * Real.log x)| ≤ B / (Real.log x) ^ 2 := by
    rw [abs_div, abs_of_pos (mul_pos hx0 hl0)]
    calc
      _ ≤ (B * x / (Real.log x) ^ 2) / (x * Real.log x) :=
        div_le_div_of_nonneg_right (ha x hxa) (mul_pos hx0 hl0).le
      _ = (B / (Real.log x) ^ 2) / Real.log x := by
        field_simp (disch := simp only [hx0.ne', hl0.ne', ne_eq, not_false_eq_true])
      _ ≤ B / (Real.log x) ^ 2 := div_le_self (div_nonneg hB (sq_nonneg _)) hl
  have htail :=
    abs_integral_psiLogErrorKernel_Ioi_le hB ((by norm_num only : (1 : ℝ) < 2).trans_le hx) hl
      (fun t ht ↦ ha t (hxa.trans ht))
  rw [sub_add_eq_sub_sub, mangoldtLogSum_error_eq_tail ⟨B, hB, hb⟩ hx]
  calc
    _ ≤ _ := abs_sub _ _
    _ ≤ B / (Real.log x) ^ 2 + B / (Real.log x) ^ 2 := add_le_add hboundary htail
    _ = 2 * B / (Real.log x) ^ 2 := by ring

/-- A second-order psi bound and identification of the integral constant with Euler's
constant imply the required second-order logarithmic Mangoldt bound.
Bound the boundary and tail separately by the psi constant divided by log squared;
their sum gives twice that constant. Only the constant identification remains additional. -/
theorem mangoldtSecondOrder_of_constant (hψ : PsiSecondOrderBound)
    (hc : psiMertensConstant = Real.eulerMascheroniConstant) : MangoldtLogSumSecondOrderBound := by
  simpa only [MangoldtLogSumSecondOrderBound, hc] using mangoldtLogSum_error_bound hψ

/-- Under a second-order psi estimate, the logarithmic Mangoldt sum minus log-log
converges to the integral constant. Squeeze the norm of the difference using the proved
inverse-log-square error and logarithmic divergence. This identifies the limit uniquely. -/
theorem tendsto_mangoldtLogSum_constant (hψ : PsiSecondOrderBound) :
    Filter.Tendsto
      (fun x : ℝ ↦
        (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)) -
          Real.log (Real.log x))
      Filter.atTop (nhds psiMertensConstant) := by
  obtain ⟨A, _, hb⟩ := mangoldtLogSum_error_bound hψ
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := (Real.tendsto_log_atTop.atTop_mul_atTop₀ Real.tendsto_log_atTop).const_div_atTop A
  simp only [← pow_two] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall (fun x ↦ norm_nonneg _)) ?_ ht
  filter_upwards [hb] with x hx
  simpa only [Real.norm_eq_abs, sub_add_eq_sub_sub] using hx

/-- A second-order psi estimate upgrades qualitative convergence to Euler's constant
into the quantitative Mangoldt estimate required by the value criteria.
Uniqueness of the limit identifies the integral constant, then the error bound applies.
The qualitative Euler-constant limit remains an explicit hypothesis. -/
theorem mangoldtSecondOrder_of_tendsto (hψ : PsiSecondOrderBound)
    (hl :
      Filter.Tendsto
        (fun x : ℝ ↦
          (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)) -
            Real.log (Real.log x))
        Filter.atTop (nhds Real.eulerMascheroniConstant)) :
    MangoldtLogSumSecondOrderBound := by
  exact
    mangoldtSecondOrder_of_constant hψ (tendsto_nhds_unique (tendsto_mangoldtLogSum_constant hψ) hl)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
