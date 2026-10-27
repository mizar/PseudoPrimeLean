/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RiemannChebyshevNumericalBounds
public import PseudoPrime.LLS.GammaKernel
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialMangoldtBounds

/-! # Explicit finite Gamma-kernel principal sums

The exponential Abel comparison bounds the finite level-one sum with error 38x^(1/4).
An exact missing-prime-factor identity supplies the numerical correction at every level.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At positive scale and positive index, the real level-one Gamma summand
is the exponential Mangoldt term divided by sqrt(x). Apply the inverse-Mellin
transform identity and cancel the positive square-root factors. -/
private theorem gamma_level_one_term_eq_exponential {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re =
      Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hu : 0 < (n : ℝ) / x := div_pos hnpos hx
  simp only [MellinKernel.summand, ite_eq_right hn,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [gamma_transform_of_function gammaMellinKernel rfl hu, Real.sqrt_div hnpos.le, neg_div]
  field_simp (discharger :=
    first
    | exact (Real.sqrt_pos.mpr hnpos).ne'
    | exact (Real.sqrt_pos.mpr hx).ne')

/-- A principal Gamma summand agrees with its level-one value on indices
coprime to the level and vanishes otherwise. Use the principal character's
unit and nonunit values. This identifies its finite missing-prime-factor sum. -/
private theorem gamma_principal_term_eq_level_one_or_zero {q n : ℕ} (x : ℝ) (hn : n ≠ 0) :
    (gammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re =
      if Nat.Coprime n q then (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re
      else 0 := by
  by_cases hc : Nat.Coprime n q
  · have hu := (ZMod.isUnit_iff_coprime n q).mpr hc
    simp only [ite_eq_left hc, MellinKernel.summand, ite_eq_right hn, MulChar.one_apply hu,
      MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1))]
  · have hu : ¬IsUnit (n : ZMod q) := fun h ↦ hc ((ZMod.isUnit_iff_coprime n q).mp h)
    simp only [ite_eq_right hc, MellinKernel.summand, ite_eq_right hn,
      MulChar.map_nonunit (1 : DirichletCharacter ℂ q) hu, mul_zero, zero_mul, Complex.zero_re]

/-- At positive scale, the finite real Gamma-kernel sum for the level-one
principal character equals the exponential Mangoldt sum divided by sqrt(x).
Apply the term identity on positive indices and remove the zero Mangoldt term.
This transfers the quantitative Abel estimate to the paper's actual summands. -/
theorem gamma_level_one_sum_eq_exponential {x y : ℝ} (hx : 0 < x) :
    (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) =
      AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x y / Real.sqrt x := by
  unfold AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp only [Nat.cast_zero, neg_zero, zero_div, Real.exp_zero, ArithmeticFunction.map_zero,
    mul_zero, zero_add]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  exact gamma_level_one_term_eq_exponential hx (Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1)

/-- At positive scale, the finite difference between the level-one and
level-q principal Gamma sums equals the missing exponential Mangoldt sum divided
by sqrt(x). Split the principal character into unit and nonunit cases termwise.
This exposes the exact finite modulus correction before numerical estimation. -/
theorem gamma_principal_sum_level_difference {q : ℕ} {x y : ℝ} (hx : 0 < x) :
    (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
        (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re) =
      AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x y q / Real.sqrt x := by
  classical
  unfold AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum
  rw [← Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1
  rw [gamma_principal_term_eq_level_one_or_zero (q := q) x hn0]
  by_cases hc : Nat.Coprime n q
  · rw [ite_eq_left hc, ite_eq_right (not_not.mpr hc), sub_self]
  · rw [ite_eq_right hc, ite_eq_left hc, sub_zero]
    exact gamma_level_one_term_eq_exponential hx hn0

/-- Under RH, at x>0 and nonnegative cutoff multiplier lambda, the actual
finite level-one Gamma sum is at least sqrt(x)(1-exp(-lambda))-38x^(1/4).
The uniform Chebyshev estimate and common-envelope Abel cancellation give 38
instead of the separated error allowance 76. There is no eventual threshold. -/
theorem gamma_level_one_sum_lower (hRH : RiemannHypothesis) {x lambda : ℝ} (hx : 0 < x)
    (hl : 0 ≤ lambda) :
    Real.sqrt x * (1 - Real.exp (-lambda)) - 38 * x ^ (1 / 4 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊lambda * x⌋₊,
        (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  have h :=
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum_div_sqrt_lower_of_psi_error
      (by norm_num only : (0 : ℝ) ≤ 38) hx (mul_nonneg hl hx.le)
      (fun t ht ↦ LLS.psi_error_le_thirty_eight hRH ht)
  rw [neg_div, mul_div_cancel_right₀ _ hx.ne'] at h
  rw [gamma_level_one_sum_eq_exponential hx]
  exact h

/-- Under RH, for nonzero modulus q, positive scale and cutoff lambda*x≥1,
the finite principal Gamma sum has main term sqrt(x)(1-exp(-lambda)), truncation
error 38x^(1/4), and modulus error log(q)log(lambda*x)/(log(2)sqrt(x)).
Combine the exact finite level correction with the elementary prime-power count.
All constants and cutoff requirements are explicit. -/
theorem gamma_principal_sum_lower (hRH : RiemannHypothesis) {q : ℕ} [NeZero q] {x lambda : ℝ}
    (hx : 0 < x) (hl : 0 ≤ lambda) (hcut : 1 ≤ lambda * x) :
    Real.sqrt x * (1 - Real.exp (-lambda)) - 38 * x ^ (1 / 4 : ℝ) -
        Real.log q * Real.log (lambda * x) / (Real.log 2 * Real.sqrt x) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊lambda * x⌋₊,
        (gammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re := by
  have hlevel := gamma_level_one_sum_lower hRH hx hl
  have hdiff := gamma_principal_sum_level_difference (q := q) (y := lambda * x) hx
  have hloss :=
    div_le_div_of_nonneg_right
      (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum_le_log_product hx (NeZero.ne q)
        hcut)
      (Real.sqrt_nonneg x)
  rw [div_div] at hloss
  linarith only [hlevel, hdiff, hloss]

/-- Under RH, at x>0 and nonnegative cutoff multiplier lambda, the actual
finite level-one Gamma sum is at least sqrt(x)(1-exp(-lambda))-13x^(1/4).
The uniform Chebyshev estimate and common-envelope Abel cancellation give 13
by combining the endpoint and integral errors. There is no eventual threshold. -/
theorem gamma_level_one_sum_lower_thirteen (hRH : RiemannHypothesis) {x lambda : ℝ} (hx : 0 < x)
    (hl : 0 ≤ lambda) :
    Real.sqrt x * (1 - Real.exp (-lambda)) - 13 * x ^ (1 / 4 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊lambda * x⌋₊,
        (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  have h :=
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum_div_sqrt_lower_of_psi_error
      (by norm_num only : (0 : ℝ) ≤ 13) hx (mul_nonneg hl hx.le)
      (fun t ht ↦ LLS.psi_error_le_thirteen hRH ht)
  rw [neg_div, mul_div_cancel_right₀ _ hx.ne'] at h
  rw [gamma_level_one_sum_eq_exponential hx]
  exact h

/-- Under RH, for nonzero modulus q, positive scale and cutoff lambda*x≥1,
the finite principal Gamma sum has main term sqrt(x)(1-exp(-lambda)), truncation
error 13x^(1/4), and modulus error log(q)log(lambda*x)/(log(2)sqrt(x)).
Combine the exact finite level correction with the elementary prime-power count.
All constants and cutoff requirements are explicit. -/
theorem gamma_principal_sum_lower_thirteen (hRH : RiemannHypothesis) {q : ℕ} [NeZero q]
    {x lambda : ℝ} (hx : 0 < x) (hl : 0 ≤ lambda) (hcut : 1 ≤ lambda * x) :
    Real.sqrt x * (1 - Real.exp (-lambda)) - 13 * x ^ (1 / 4 : ℝ) -
        Real.log q * Real.log (lambda * x) / (Real.log 2 * Real.sqrt x) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊lambda * x⌋₊,
        (gammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re := by
  have hlevel := gamma_level_one_sum_lower_thirteen hRH hx hl
  have hdiff := gamma_principal_sum_level_difference (q := q) (y := lambda * x) hx
  have hloss :=
    div_le_div_of_nonneg_right
      (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum_le_log_product hx (NeZero.ne q)
        hcut)
      (Real.sqrt_nonneg x)
  rw [div_div] at hloss
  linarith only [hlevel, hdiff, hloss]

end PseudoPrime.LLS.PaperStatements
