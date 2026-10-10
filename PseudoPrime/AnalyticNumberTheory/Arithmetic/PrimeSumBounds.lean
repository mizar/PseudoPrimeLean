/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.Analysis.LogPowerAsymptotics
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt

/-! Unconditional second-order estimates needed for weighted prime sums. -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Unconditional second-order prime number estimate for Chebyshev's psi function.
There exists a nonnegative real constant bounding `|psi x - x|` by
`B * x / (log x)^2` for all sufficiently large real `x`.
No RH hypothesis is included. This is an explicit arithmetic input to the value criteria. -/
def PsiSecondOrderBound : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ x : ℝ in Filter.atTop, |Chebyshev.psi x - x| ≤ B * x / (Real.log x) ^ 2

/-- Unconditional second-order estimate for the logarithmically weighted Mangoldt sum.
There exists a nonnegative real constant bounding the difference from
`log log x + Euler's constant` by `A / (log x)^2` eventually at infinity.
The natural floor cuts off the sum; the term at one is zero with Lean's total division.
This is an explicit arithmetic input, including identification of the Euler constant. -/
def MangoldtLogSumSecondOrderBound : Prop :=
  ∃ A : ℝ,
    0 ≤ A ∧
      ∀ᶠ x : ℝ in Filter.atTop,
        |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)) -
              (Real.log (Real.log x) + Real.eulerMascheroniConstant)| ≤
          A / (Real.log x) ^ 2

/-- For cutoff at least one, the reciprocal Mangoldt sum is at most `log x * (1 + log x)`.
Bound each Mangoldt coefficient by its logarithm, then use the harmonic-number bound.
This controls the arithmetic contribution to the uniform truncation error. -/
theorem reciprocalMangoldtSum_le_log {x : ℝ} (hx : 1 ≤ x) :
    reciprocalMangoldtSum x ≤ Real.log x * (1 + Real.log x) := by
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hterm : reciprocalMangoldtSum x ≤ Real.log x * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (n : ℝ)⁻¹ := by
    unfold reciprocalMangoldtSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1
    have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff (zero_le_one.trans hx)).mp (Finset.mem_Ioc.mp hn).2
    rw [← div_eq_mul_inv]
    exact
      div_le_div_of_nonneg_right
        (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 hnx)) hn0.le
  have hsum : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (n : ℝ)⁻¹) = (harmonic ⌊x⌋₊ : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [← Finset.Icc_add_one_left_eq_Ioc]
    simp only [zero_add]
  rw [hsum] at hterm
  exact hterm.trans (mul_le_mul_of_nonneg_left (harmonic_floor_le_one_add_log x hx) hl)

/-- The reciprocal Mangoldt majorant is nonnegative for every real cutoff.
Each coefficient and denominator is nonnegative. This supplies the lower bound
in the squeeze argument for the scaled arithmetic error. -/
theorem reciprocalMangoldtSum_nonneg (x : ℝ) : 0 ≤ reciprocalMangoldtSum x := by
  exact
    Finset.sum_nonneg
      (fun n _ ↦ div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))

/-- The reciprocal Mangoldt majorant divided by `sqrt x * log x` tends to zero.
Squeeze it between zero and `(1 + log x) / sqrt x`, using logarithmic growth
relative to a positive power. This removes the arithmetic part of the truncation error. -/
theorem tendsto_reciprocalMangoldtSum_scaled :
    Filter.Tendsto (fun x : ℝ ↦ reciprocalMangoldtSum x / (Real.sqrt x * Real.log x)) Filter.atTop
      (nhds 0) := by
  have hlog : Filter.Tendsto (fun x : ℝ ↦ Real.log x / Real.sqrt x) Filter.atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num only : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hone : Filter.Tendsto (fun x : ℝ ↦ 1 / Real.sqrt x) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hb : Filter.Tendsto (fun x : ℝ ↦ (1 + Real.log x) / Real.sqrt x) Filter.atTop (nhds 0) := by
    simpa only [add_div, zero_add] using hone.add hlog
  apply squeeze_zero' ?_ ?_ hb
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact
      div_nonneg (reciprocalMangoldtSum_nonneg x)
        (mul_nonneg (Real.sqrt_nonneg x) (Real.log_nonneg hx.le))
  · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr (zero_lt_one.trans hx)).ne'
    have h :=
      div_le_div_of_nonneg_right (reciprocalMangoldtSum_le_log hx.le)
        (mul_nonneg (Real.sqrt_nonneg x) (Real.log_nonneg hx.le))
    convert h using 1
    field_simp (disch := simp only [hl, hs, ne_eq, not_false_eq_true])

/-- For any cutoff, split the truncated majorant into the Mangoldt logarithmic sum minus
`psi x / (x log x)`. Distribute the finite sum over the weight difference.
This identifies precisely the two arithmetic quantities required for sharp value estimates. -/
theorem truncatedMangoldtMajorant_eq_log_sum_sub_psi {x : ℝ} :
    truncatedMangoldtMajorant x =
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)) -
        Chebyshev.psi x / (x * Real.log x) := by
  unfold truncatedMangoldtMajorant Chebyshev.psi
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- For a cutoff above one, logarithmic Mangoldt-sum error at most `a` and Chebyshev-psi
error at most `b` give majorant error at most `a + b / (x log x)` around
`log log x + gamma - 1 / log x`. Split the majorant and combine the two absolute bounds.
This transfers quantitative prime-sum estimates to the general L-value arithmetic term. -/
theorem abs_truncatedMangoldtMajorant_error_le {x a b : ℝ} (hx : 1 < x)
    (ha :
      |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)) -
            (Real.log (Real.log x) + Real.eulerMascheroniConstant)| ≤
        a)
    (hb : |Chebyshev.psi x - x| ≤ b) :
    |truncatedMangoldtMajorant x -
          (Real.log (Real.log x) + Real.eulerMascheroniConstant - 1 / Real.log x)| ≤
      a + b / (x * Real.log x) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hl : 0 < Real.log x := Real.log_pos hx
  have hc : x / (x * Real.log x) = 1 / Real.log x := by
    field_simp (disch := simp only [hx0.ne', hl.ne', ne_eq, not_false_eq_true])
  have hd : |(Chebyshev.psi x - x) / (x * Real.log x)| ≤ b / (x * Real.log x) := by
    rw [abs_div, abs_of_pos (mul_pos hx0 hl)]
    exact div_le_div_of_nonneg_right hb (mul_pos hx0 hl).le
  rw [sub_div] at hd
  rw [truncatedMangoldtMajorant_eq_log_sum_sub_psi]
  apply abs_le.mpr
  constructor <;>
    linarith only [(abs_le.mp ha).1, (abs_le.mp ha).2, (abs_le.mp hd).1, (abs_le.mp hd).2, hc]

/-- The reciprocal Mangoldt majorant multiplied by `log x / sqrt x` tends to zero.
Use its logarithmic upper bound and the zero limits of the second and third logarithmic powers.
This controls the arithmetic contribution after multiplying the truncation error by `log^2 x`. -/
theorem tendsto_reciprocalMangoldtSum_mul_log_div_sqrt :
    Filter.Tendsto (fun x : ℝ ↦ reciprocalMangoldtSum x * Real.log x / Real.sqrt x) Filter.atTop
      (nhds 0) := by
  have hb :
    Filter.Tendsto (fun x : ℝ ↦ (Real.log x) ^ 2 * (1 + Real.log x) / Real.sqrt x) Filter.atTop
      (nhds 0) := by
    have heq :
      (fun x : ℝ ↦ (Real.log x) ^ 2 * (1 + Real.log x) / Real.sqrt x) =
        (fun x : ℝ ↦ (Real.log x) ^ 2 / Real.sqrt x + (Real.log x) ^ 3 / Real.sqrt x) := by
      funext x
      ring
    rw [heq]
    simpa only [zero_add] using
      (Analysis.tendsto_log_pow_div_sqrt 2).add (Analysis.tendsto_log_pow_div_sqrt 3)
  apply squeeze_zero' ?_ ?_ hb
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    exact
      div_nonneg (mul_nonneg (reciprocalMangoldtSum_nonneg x) (Real.log_nonneg hx))
        (Real.sqrt_nonneg x)
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have h :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (reciprocalMangoldtSum_le_log hx) (Real.log_nonneg hx))
        (Real.sqrt_nonneg x)
    convert h using 1
    ring

/-- For a cutoff above one and a positive index below the cutoff, the truncated Mangoldt
weight is nonnegative. The index one contributes zero; for larger indices, monotonicity
of the logarithm compares the two denominators. This removes absolute values in sums. -/
theorem truncatedMangoldtTerm_nonneg {x : ℝ} (hx : 1 < x) {n : ℕ} (hn : n ∈ Finset.Ioc 0 ⌊x⌋₊) :
    0 ≤ ArithmeticFunction.vonMangoldt n * (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x)) := by
  by_cases hn1 : n = 1
  · subst n
    simp only [ArithmeticFunction.vonMangoldt_apply_one, zero_mul, le_refl]
  · have hn2 : 1 < (n : ℝ) := by
      exact_mod_cast (lt_of_le_of_ne (Finset.mem_Ioc.mp hn).1 (Ne.symm hn1))
    have hnx : (n : ℝ) ≤ x :=
      (Nat.le_floor_iff (zero_lt_one.trans hx).le).mp (Finset.mem_Ioc.mp hn).2
    have hln : 0 < Real.log (n : ℝ) := Real.log_pos hn2
    have hm : (n : ℝ) * Real.log n ≤ x * Real.log x :=
      mul_le_mul hnx (Real.log_le_log (zero_lt_one.trans hn2) hnx) hln.le (zero_lt_one.trans hx).le
    exact
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (sub_nonneg.mpr (one_div_le_one_div_of_le (mul_pos (zero_lt_one.trans hn2) hln) hm))

/-- For cutoff above one with logarithm at least one, logarithmic Mangoldt error bounded by
`A/log^2 x` and psi error bounded by `B x/log^2 x`, with nonnegative `B`, give
`Q(x) <= log log x + gamma - 1/log x + (A+B)/log^2 x`.
Cancel the psi cutoff factor and bound the extra reciprocal logarithm by one.
This transfers the quantitative prime-sum inputs to the arithmetic main term. -/
theorem truncatedMangoldtMajorant_le_of_secondOrder_mangoldt_errors {x A B : ℝ} (hx : 1 < x)
    (hl : 1 ≤ Real.log x) (hB : 0 ≤ B)
    (hH :
      |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)) -
            (Real.log (Real.log x) + Real.eulerMascheroniConstant)| ≤
        A / (Real.log x) ^ 2)
    (hψ : |Chebyshev.psi x - x| ≤ B * x / (Real.log x) ^ 2) :
    truncatedMangoldtMajorant x ≤
      Real.log (Real.log x) + Real.eulerMascheroniConstant - 1 / Real.log x +
        (A + B) / (Real.log x) ^ 2 := by
  have he := (abs_le.mp (abs_truncatedMangoldtMajorant_error_le hx hH hψ)).2
  have hx0 := (zero_lt_one.trans hx).ne'
  have hl0 := (Real.log_pos hx).ne'
  have hc :
    (B * x / (Real.log x) ^ 2) / (x * Real.log x) = (B / (Real.log x) ^ 2) / Real.log x := by
    field_simp (disch := simp only [hx0, hl0, ne_eq, not_false_eq_true])
  have hb := div_le_self (div_nonneg hB (sq_nonneg (Real.log x))) hl
  rw [hc] at he
  rw [add_div]
  linarith only [he, hb]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
