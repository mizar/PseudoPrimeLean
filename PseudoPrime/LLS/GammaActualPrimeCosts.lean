/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaCharacterEulerCosts

public import PseudoPrime.Analysis.GammaActualPrimeLocalCost

public import PseudoPrime.LLS.GammaDyadicEulerCertificates

public import PseudoPrime.LLS.GammaOddConductorBudget

/-! # Actual prime losses with arbitrary positive-power prefixes -/

@[expose] public section

namespace PseudoPrime.LLS

/-- When chi(p)=-1, the actual local loss for any positive-power Euler
prefix is at most log p times the certified square-prime allowance.
Combine the full parity-cancelled Euler bound with the signed ramp bound.
This supplies the actual local input for conductor-gap absorption. -/
theorem gamma_actual_minus_one_prime_cost_le {f p : ℕ} (χ : DirichletCharacter ℂ f) (hp : p.Prime)
    (hχ : χ p = -1) (K : Finset ℕ) {x : ℝ} (hx : 0 < x) :
    Analysis.gammaActualPrimeLocalCost χ p K x ≤
      Real.log p * Analysis.gammaSquareCombinedCost p x := by
  have he := Analysis.gamma_minus_one_positive_prime_correction_le_cost χ hp hχ K
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hr := mul_le_mul_of_nonneg_left (Analysis.gamma_ramp_neg_one_series_le_count hp.one_lt hx) hl
  dsimp only [Analysis.gammaActualPrimeLocalCost, Analysis.gammaSquareCombinedCost]
  rw [hχ]
  nlinarith only [he, hr]

/-- If chi(p)=1, all Euler corrections vanish and the actual local ramp
loss is nonpositive. The bound W<=exp(-u) proves this term by term, and
absolute convergence permits the infinite comparison. This accounts for
the cost-free branch without dropping its signed arithmetic contribution. -/
theorem gamma_actual_one_prime_cost_nonpos {f p : ℕ} (χ : DirichletCharacter ℂ f) (hp : p.Prime)
    (hχ : χ p = 1) (K : Finset ℕ) {x : ℝ} (hx : 0 < x) :
    Analysis.gammaActualPrimeLocalCost χ p K x ≤ 0 := by
  have hr :
    (∑' k : ℕ, Analysis.exponentialRampLocalCorrection 1 ((p : ℝ) ^ (k + 1) / x) (k + 1)) ≤ 0 := by
    apply tsum_nonpos
    intro k
    simp only [Analysis.exponentialRampLocalCorrection, one_pow, Complex.add_re, Complex.one_re]
    linarith only [(Analysis.exponentialRampWeight_bounds ((p : ℝ) ^ (k + 1) / x)).2]
  dsimp only [Analysis.gammaActualPrimeLocalCost]
  simp only [map_pow, hχ, one_pow, Complex.one_re, sub_self, zero_mul, Finset.sum_const_zero,
    zero_add]
  exact
    mul_nonpos_of_nonneg_of_nonpos (Real.log_nonneg (by exact_mod_cast hp.one_le))
      (div_nonpos_of_nonpos_of_nonneg hr (Real.sqrt_pos.mpr hx).le)

/-- For chi(2)=-1 and all x>=10000, the actual dyadic loss of an arbitrary
positive-power prefix, minus M log four, is at most 12/25. Use the exact
full Euler parity cancellation and the signed ramp certificate. -/
theorem gamma_actual_dyadic_minus_one_cost_le {f : ℕ} (χ : DirichletCharacter ℂ f) (hχ : χ 2 = -1)
    (K : Finset ℕ) {x : ℝ} (hx : 10000 ≤ x) :
    Analysis.gammaActualPrimeLocalCost χ 2 K x - (11783423 / 25000000 : ℝ) * Real.log 4 ≤
      (12 / 25 : ℝ) := by
  have he := Analysis.gamma_minus_one_positive_prime_correction_le_cost χ Nat.prime_two hχ K
  have hr := gamma_dyadic_minus_one_actual_ramp_le hx
  have hc := gamma_dyadic_weighted_euler_bounds.2
  norm_num only [Nat.cast_ofNat] at he
  dsimp only [Analysis.gammaActualPrimeLocalCost]
  rw [show χ ((2 : ℕ) : ZMod f) = -1 by simpa only [Nat.cast_ofNat] using hχ]
  norm_num only [Nat.cast_ofNat]
  linarith only [he, hr, hc]

end PseudoPrime.LLS
