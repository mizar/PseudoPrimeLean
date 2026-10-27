/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64DyadicEulerBounds
public import PseudoPrime.Analysis.DyadicRampSmallScale

/-! # Actual dyadic losses for the first phase candidate -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a signed node list, a character, a prime, a finite set of positive powers,
and a scale. Output: the actual finite Euler loss plus the full signed ramp loss.
Role: group local contributions without discarding coefficient or parity cancellation. -/
noncomputable def finiteSignedActualPrimeLocalCost (l : List (ℚ × ℚ)) {f : ℕ}
    (χ : DirichletCharacter ℂ f) (p : ℕ) (K : Finset ℕ) (x : ℝ) : ℝ :=
  (∑ k ∈ K, (1 - (χ (p ^ (k + 1))).re) * finiteSignedMangoldtWeight l (p ^ (k + 1))) +
    Real.log p *
      ((∑' k : ℕ, exponentialRampLocalCorrection (χ p) ((p : ℝ) ^ (k + 1) / x) (k + 1)) /
        Real.sqrt x)

/-- If the character is one at a prime and the scale is positive, its actual local
cost is nonpositive for every signed node list. Euler corrections vanish; each ramp
correction is nonpositive. This supplies the cost-free local branch. -/
theorem finiteSigned_actual_one_prime_cost_nonpos (l : List (ℚ × ℚ)) {f p : ℕ}
    (χ : DirichletCharacter ℂ f) (hp : p.Prime) (hχ : χ p = 1) (K : Finset ℕ) {x : ℝ} (hx : 0 < x) :
    finiteSignedActualPrimeLocalCost l χ p K x ≤ 0 := by
  have hr : (∑' k : ℕ, exponentialRampLocalCorrection 1 ((p : ℝ) ^ (k + 1) / x) (k + 1)) ≤ 0 := by
    apply tsum_nonpos
    intro k
    simp only [exponentialRampLocalCorrection, one_pow, Complex.add_re, Complex.one_re]
    linarith only [(exponentialRampWeight_bounds ((p : ℝ) ^ (k + 1) / x)).2]
  dsimp only [finiteSignedActualPrimeLocalCost]
  simp only [map_pow, hχ, one_pow, Complex.one_re, sub_self, zero_mul, Finset.sum_const_zero,
    zero_add]
  exact
    mul_nonpos_of_nonneg_of_nonpos (Real.log_nonneg (by exact_mod_cast hp.one_le))
      (div_nonpos_of_nonpos_of_nonneg hr (Real.sqrt_pos.mpr hx).le)

/-- For character value zero at two and scale at least 1600, any finite positive-power
prefix has phase-candidate local cost at most 427/500. Combine the signed Euler
certificate with the continuous ramp envelope; no finite scale enumeration is used. -/
theorem phase64_actual_dyadic_zero_cost_le {f : ℕ} (χ : DirichletCharacter ℂ f) (hχ : χ 2 = 0)
    (K : Finset ℕ) {x : ℝ} (hx : 1600 ≤ x) :
    finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ 2 K x ≤ (427 / 500 : ℝ) := by
  have he := phase64_dyadic_zero_prefix_le χ hχ K
  have hr := dyadic_zero_ramp_le_of_ge_1600 hx
  dsimp only [finiteSignedActualPrimeLocalCost]
  rw [show χ ((2 : ℕ) : ZMod f) = 0 by simpa only [Nat.cast_ofNat] using hχ]
  norm_num only [Nat.cast_ofNat]
  linarith only [he, hr]

/-- For character value minus one at two and scale at least 1600, the actual phase
cost minus the coefficient mass times log four is at most 473/1000. Exact odd-power
cancellation and the ramp envelope retain the conductor allowance explicitly. -/
theorem phase64_actual_dyadic_minus_one_cost_le {f : ℕ} (χ : DirichletCharacter ℂ f) (hχ : χ 2 = -1)
    (K : Finset ℕ) {x : ℝ} (hx : 1600 ≤ x) :
    finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ 2 K x -
        (90992831 / 200000000 : ℝ) * Real.log 4 ≤
      (473 / 1000 : ℝ) := by
  have he := phase64_dyadic_minus_one_prefix_le χ hχ K
  have hr := dyadic_minus_one_ramp_le_of_ge_1600 hx
  dsimp only [finiteSignedActualPrimeLocalCost]
  rw [show χ ((2 : ℕ) : ZMod f) = -1 by simpa only [Nat.cast_ofNat] using hχ]
  norm_num only [Nat.cast_ofNat]
  linarith only [he, hr]

end PseudoPrime.Analysis
