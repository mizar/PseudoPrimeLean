/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.Analytic.Order

/-!
# Simple zeros of the reciprocal Gamma function

The entire reciprocal Gamma function has a simple zero at each nonpositive integer.
These orders determine the trivial-zero contributions in Dirichlet explicit formulas.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- The reciprocal Gamma recurrence differentiates everywhere, including its zeros.
The shifted factor is entire, so the product rule applies without pole exclusions. -/
theorem deriv_inverseGamma (z : ℂ) :
    deriv (fun s : ℂ => (Complex.Gamma s)⁻¹) z =
      (Complex.Gamma (z + 1))⁻¹ + z * deriv (fun s : ℂ => (Complex.Gamma s)⁻¹) (z + 1) := by
  simpa only [one_mul, mul_one, Function.comp_apply, id_eq] using
    (((hasDerivAt_id z).mul
            ((Complex.differentiable_one_div_Gamma (z + 1)).hasDerivAt.comp z
              ((hasDerivAt_id z).add_const 1))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one)).deriv

/-- At every nonpositive integer the reciprocal Gamma derivative is nonzero.
The recurrence starts with derivative one at zero and multiplies by a nonzero
negative integer at each subsequent zero. This identifies the zeros as simple. -/
theorem deriv_inverseGamma_neg_nat_ne_zero (n : ℕ) :
    deriv (fun s : ℂ => (Complex.Gamma s)⁻¹) (-(n : ℂ)) ≠ 0 := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, neg_zero, deriv_inverseGamma]
    simpa only [zero_add, Complex.Gamma_one, inv_one, zero_mul, add_zero] using
      (one_ne_zero : (1 : ℂ) ≠ 0)
  | succ n
    ih =>
    have hz : (-(↑(n + 1) : ℂ)) + 1 = -(n : ℂ) := by
      rw [Nat.cast_add, Nat.cast_one, neg_add, neg_add_cancel_right]
    rw [deriv_inverseGamma, hz, Complex.Gamma_neg_nat_eq_zero, inv_zero, zero_add]
    exact mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))) ih

/-- The entire reciprocal Gamma function has analytic order one at `-n`.
Its value vanishes there and its derivative does not; the result supplies the
local order needed for exact trivial-zero residues. -/
theorem analyticOrderAt_inverseGamma_neg_nat (n : ℕ) :
    analyticOrderAt (fun s : ℂ => (Complex.Gamma s)⁻¹) (-(n : ℂ)) = 1 := by
  exact
    AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (Complex.differentiable_one_div_Gamma.analyticAt _)
      (by rw [Complex.Gamma_neg_nat_eq_zero, inv_zero]) (deriv_inverseGamma_neg_nat_ne_zero n)

/-- The reciprocal real archimedean Gamma factor has a simple zero at `-2n`.
The nonvanishing power of pi preserves the order, and the affine argument
`s / 2` has nonzero derivative. This covers even-character trivial zeros. -/
theorem analyticOrderAt_inverseGammaReal_neg_two_nat (n : ℕ) :
    analyticOrderAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) (-2 * (n : ℂ)) = 1 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpall : Differentiable ℂ (fun s : ℂ => ((Real.pi : ℂ) ^ (-s / 2))⁻¹) := fun z =>
    ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow (Or.inl hpi)).inv
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi))
  have hp := hpall.analyticAt (-2 * (n : ℂ))
  have hg :
    AnalyticAt ℂ ((fun s : ℂ => (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ => s / 2)) (-2 * (n : ℂ)) :=
    (Complex.differentiable_one_div_Gamma.comp (differentiable_id.div_const 2)).analyticAt _
  have heq :
    (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) =
      (fun s : ℂ => ((Real.pi : ℂ) ^ (-s / 2))⁻¹) *
        ((fun s : ℂ => (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ => s / 2)) := by
    funext s
    exact mul_inv ((Real.pi : ℂ) ^ (-s / 2)) (Complex.Gamma (s / 2))
  rw [heq, analyticOrderAt_mul hp hg,
    hp.analyticOrderAt_eq_zero.mpr (inv_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi))),
    zero_add]
  have ha : AnalyticAt ℂ (fun s : ℂ => s / 2) (-2 * (n : ℂ)) := analyticAt_id.div_const
  have hd : deriv (fun s : ℂ => s / 2) (-2 * (n : ℂ)) ≠ 0 := by
    have he := ((hasDerivAt_id (-2 * (n : ℂ))).div_const 2).deriv
    simp only [id_eq] at he
    exact he.trans_ne (div_ne_zero one_ne_zero two_ne_zero)
  rw [analyticOrderAt_comp_of_deriv_ne_zero ha hd]
  have hz : -2 * (n : ℂ) / 2 = -(n : ℂ) := by ring
  rw [hz]
  exact analyticOrderAt_inverseGamma_neg_nat n

end PseudoPrime.AnalyticNumberTheory.Gamma
