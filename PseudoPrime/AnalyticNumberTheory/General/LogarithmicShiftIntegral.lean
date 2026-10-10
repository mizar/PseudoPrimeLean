/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.LogarithmicMellinInversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integration of shifted logarithmic sums

Integrating the Mellin shift from one to infinity converts the arithmetic coefficients
into the logarithmic L-value weights. The coefficient at one must vanish.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For n>1, rewrite n^(-sigma) as an exponential with a negative real rate.
This elementary identity prepares half-line integration. -/
theorem cpow_neg_real_eq_exp {n : ℝ} (hn : 1 < n) (σ : ℝ) :
    (n : ℂ) ^ (-(σ : ℂ)) = Complex.exp (-(Real.log n : ℂ) * σ) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one hn))),
    ← Complex.ofReal_log (le_of_lt (lt_trans zero_lt_one hn))]
  congr 1
  ring

/-- For n>1, n^(-sigma) is integrable on sigma>1. Exponential decay supplies the
integrability needed for finite logarithmic sums. -/
theorem integrableOn_cpow_neg_real {n : ℝ} (hn : 1 < n) :
    MeasureTheory.IntegrableOn (fun σ : ℝ ↦ (n : ℂ) ^ (-(σ : ℂ))) (Set.Ioi 1) := by
  have hneg : (-(Real.log n : ℂ)).re < 0 := by
    rw [Complex.neg_re, Complex.ofReal_re]
    exact neg_neg_of_pos (Real.log_pos hn)
  simpa only [cpow_neg_real_eq_exp hn] using integrableOn_exp_mul_complex_Ioi hneg 1

/-- For n>1, integrating n^(-sigma) over sigma>1 gives 1/(n log n).
The exponential integral computes the coefficient in logarithmic L-value sums. -/
theorem integral_cpow_neg_real {n : ℝ} (hn : 1 < n) :
    (∫ σ : ℝ in Set.Ioi 1, (n : ℂ) ^ (-(σ : ℂ))) = (n : ℂ)⁻¹ / (Real.log n : ℂ) := by
  have hneg : (-(Real.log n : ℂ)).re < 0 := by
    rw [Complex.neg_re, Complex.ofReal_re]
    exact neg_neg_of_pos (Real.log_pos hn)
  simp only [cpow_neg_real_eq_exp hn]
  rw [integral_exp_mul_complex_Ioi hneg, Complex.ofReal_one, mul_one, Complex.exp_neg, ←
    Complex.ofReal_exp, Real.exp_log (lt_trans zero_lt_one hn)]
  ring

/-- If the coefficient at one vanishes and n>0, each shifted logarithmic term is integrable.
The n=1 term is zero; all other terms decay exponentially in the shift. -/
theorem integrableOn_shifted_log_term (a : ℕ → ℂ) (ha : a 1 = 0) (x : ℝ) {n : ℕ} (hn : 0 < n) :
    MeasureTheory.IntegrableOn
      (fun σ : ℝ ↦ shiftedLSeriesCoefficient a σ n * (Real.log (x / n) : ℂ)) (Set.Ioi 1) := by
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hn) with hn1 | rfl
  · have hnreal : (1 : ℝ) < n := by exact_mod_cast hn1
    exact ((integrableOn_cpow_neg_real hnreal).const_mul (a n)).mul_const _
  · simp only [shiftedLSeriesCoefficient, ha, zero_mul]
    exact MeasureTheory.integrable_zero ℝ ℂ _

/-- For coefficients vanishing at one and n>0, integrate a shifted logarithmic term to
obtain the coefficient a(n)/(n log n) times log(x/n). The n=1 case remains zero. -/
theorem integral_shifted_log_term (a : ℕ → ℂ) (ha : a 1 = 0) (x : ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ σ : ℝ in Set.Ioi 1, shiftedLSeriesCoefficient a σ n * (Real.log (x / n) : ℂ)) =
      a n * ((n : ℂ)⁻¹ / (Real.log n : ℂ)) * (Real.log (x / n) : ℂ) := by
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hn) with hn1 | rfl
  · have hnreal : (1 : ℝ) < n := by exact_mod_cast hn1
    simp only [shiftedLSeriesCoefficient]
    rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul]
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
      integral_cpow_neg_real hnreal]
  · simp only [shiftedLSeriesCoefficient, ha, zero_mul, MeasureTheory.integral_zero]

/-- For coefficients vanishing at one, integration of the finite shifted logarithmic sum
produces the finite sum weighted by 1/(n log n). Termwise integrability permits exchanging
the finite sum and integral. This is the arithmetic integration step for logarithmic L-values. -/
theorem integral_logarithmicWeightedSum_shifted (a : ℕ → ℂ) (ha : a 1 = 0) (x : ℝ) :
    (∫ σ : ℝ in Set.Ioi 1, logarithmicWeightedSum (shiftedLSeriesCoefficient a σ) x) =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n * ((n : ℂ)⁻¹ / (Real.log n : ℂ)) * (Real.log (x / n) : ℂ) := by
  rw [show
      (fun σ : ℝ ↦ logarithmicWeightedSum (shiftedLSeriesCoefficient a σ) x) =
        (fun σ ↦ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, shiftedLSeriesCoefficient a σ n * (Real.log (x / n) : ℂ))
      from rfl]
  rw [MeasureTheory.integral_finsetSum _
      (fun n hn ↦ integrableOn_shifted_log_term a ha x (Finset.mem_Ioc.mp hn).1)]
  apply Finset.sum_congr rfl
  intro n hn
  exact integral_shifted_log_term a ha x (Finset.mem_Ioc.mp hn).1

/-- For coefficients vanishing at one and any real x, the finite shifted logarithmic
sum is integrable over sigma > 1. Every positive-index term is integrable, with the
index-one term zero, and a finite sum preserves integrability. This permits separating
the finite arithmetic sum from residue terms in the integrated explicit formula. -/
theorem integrableOn_logarithmicWeightedSum_shifted (a : ℕ → ℂ) (ha : a 1 = 0) (x : ℝ) :
    MeasureTheory.IntegrableOn
      (fun σ : ℝ ↦ logarithmicWeightedSum (shiftedLSeriesCoefficient a σ) x) (Set.Ioi 1) := by
  change
    MeasureTheory.IntegrableOn
      (fun σ : ℝ ↦
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, shiftedLSeriesCoefficient a σ n * (Real.log (x / n) : ℂ))
      (Set.Ioi 1)
  exact
    MeasureTheory.integrable_finsetSum _
      (fun n hn ↦ integrableOn_shifted_log_term a ha x (Finset.mem_Ioc.mp hn).1)

end PseudoPrime.AnalyticNumberTheory.General
