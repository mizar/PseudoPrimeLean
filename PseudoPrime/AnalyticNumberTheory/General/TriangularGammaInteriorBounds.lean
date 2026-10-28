/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularGammaPositiveScale
public import PseudoPrime.LLS.TriangularSignedGammaBounds

/-!
# Signed Gamma bounds inside the triangular logarithmic support

Evaluate the real-pole resolvents explicitly. At both scales the reciprocal correction
is bounded above by half an inverse square, while the negative Gamma baseline remains.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- Evaluate the regularized resolvent at a real Gamma pole and exp(-v), v nonnegative.
The indicator is supported there; convert the power to a real exponential and normalize
the denominator. This gives the elementary term used in the interior Gamma series. -/
theorem mellinResolventWeight_realPole_exp_neg {c v : ℝ} (hv : 0 ≤ v) :
    mellinResolventWeight ((-2 * c : ℝ) : ℂ) (Real.exp (-v)) =
      (((Real.exp (-2 * c * v) - 1 + 2 * c * v) / (4 * c ^ 2) : ℝ) : ℂ) := by
  have ht : Real.exp (-v) ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hv)⟩
  unfold mellinResolventWeight mellinWeightZero mellinWeightTwo
  rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, Set.indicator_of_mem ht]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow (Real.exp_pos _).le,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  rw [← Complex.ofReal_pow]
  rw [show -(-2 * c) = 2 * c by ring, show (-v) * (2 * c) = -2 * c * v by ring,
    show (-2 * c) ^ 2 = 4 * c ^ 2 by ring]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_neg, Complex.ofReal_one, div_eq_mul_inv]
  ring

/-- For a real Gamma pole, the regularized resolvent vanishes at exp(v), v nonnegative.
Treat the boundary v=0 by its exact value and the exterior by the support theorem.
This removes the terms outside the logarithmic support. -/
theorem mellinResolventWeight_realPole_exp_nonneg {c v : ℝ} (hv : 0 ≤ v) :
    mellinResolventWeight ((-2 * c : ℝ) : ℂ) (Real.exp v) = 0 := by
  rcases eq_or_lt_of_le hv with he | he
  · rw [← he]
    have h := mellinResolventWeight_realPole_exp_neg (c := c) (v := 0) le_rfl
    simpa only [neg_zero, mul_zero, Real.exp_zero, sub_self, add_zero, zero_div,
      Complex.ofReal_zero] using h
  · exact mellinResolventWeight_eq_zero_of_one_lt _ (Real.one_lt_exp_iff.mpr he)

end PseudoPrime.AnalyticNumberTheory.General
