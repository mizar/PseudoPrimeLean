/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PairedEulerExcludedBounds
public import PseudoPrime.LLS.GammaJointPrefixComparison

/-! # Witness extraction from the combined two-pole Gamma separation -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For an original character, finite Euler support and positive scale, combine the
primitive two-pole arithmetic budget with the actual original-level local correction.
Keep the conductor, the single quadratic exclusion weight and contour errors.
This is the upper side of the ramp witness comparison. -/
noncomputable def twoPoleGammaQuadraticUpper {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset ℕ)
    (x : ℝ) : ℝ :=
  Real.log χ.conductor / 2 + 419 / 50 -
      2 *
        (∑ n ∈ S,
          AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n) +
    AnalyticNumberTheory.Arithmetic.quadraticExcludedBudget χ.conductor q S
      (AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) +
    64 / 9 +
    ((7 / 6 : ℝ) * Real.log χ.conductor + 4) / Real.sqrt x +
    x ^ (-9 / 16 : ℝ) * ((3 / 2) * (Real.log χ.conductor + 28) + 1) +
    gammaQuadraticLocalCorrection χ x

/-- Twice the principal ramp lower bound minus the principal Gamma upper bound and
the two-pole quadratic upper budget. Positivity is a sufficient numerical condition
for a unit-prime witness. This defines a comparison criterion, not a certified cutoff. -/
noncomputable def twoPoleGammaSeparation {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset ℕ)
    (x : ℝ) : ℝ :=
  2 *
      ((∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x -
        gammaRampPairedErrorNumerator x / Real.sqrt x) -
    (Real.sqrt x +
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x) -
    twoPoleGammaQuadraticUpper χ S x

/-- For nonprincipal quadratic GRH data with conductor at least eight and scale at
least one, a positive two-pole separation excludes triviality on all eligible small
primes. Transfer triviality to the primitive source, retain the combined exclusion
cost, and contradict the ramp lower bound. No ambient modulus 20000 gate is used. -/
theorem gamma_ramp_prime_trivial_false_twoPole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : 8 ≤ χ.conductor) {x : ℝ}
    (hx : 1 ≤ x) (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap : 0 < twoPoleGammaSeparation χ S x) :
    ¬(∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  intro hsmall
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have ht :
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → Nat.Coprime p q → χ.primitiveCharacter p = 1 :=
    fun p hprime hpb hcop ↦
    PaperStatements.primitiveCharacter_apply_one_of_apply_one χ
      (hsmall p hprime (hprime.coprime_iff_not_dvd.mp hcop) hpb)
  have hC :=
    PaperStatements.gamma_primitive_sum_re_le_twoPole_quadratic_budget hm hGRH hp hnp
      (inv_ne_one.mpr hnp) (NumberTheory.isQuadratic_primitiveCharacter χ hquad) hx S hS ht
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann hx
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann hx
  have hN := gamma_ramp_no_witness_comparison χ hquad (zero_lt_one.trans_le hx) hsmall
  dsimp only [twoPoleGammaSeparation, twoPoleGammaQuadraticUpper] at hgap
  linarith only [hC, hT, hP, hN, hgap]

/-- Under the two-pole numerical separation and quadratic GRH assumptions, there is
a prime not dividing the original modulus through the ramp cutoff with character
value different from one. Negate the prime-triviality contradiction. This connects
the zero-mass improvement to an actual prime-witness statement. -/
theorem exists_prime_not_one_of_twoPole_separation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : 8 ≤ χ.conductor) {x : ℝ}
    (hx : 1 ≤ x) (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap : 0 < twoPoleGammaSeparation χ S x) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
  classical
  by_contra h
  apply gamma_ramp_prime_trivial_false_twoPole χ hquad hne hGRH hm hx S hS hgap
  intro p hp hd hb
  apply Classical.byContradiction
  intro hn
  exact h ⟨p, hp, hd, hb, hn⟩

/-- Under the same separation and quadratic GRH assumptions, a prime through the
cutoff has character value minus one and does not divide the original modulus.
Quadraticity and coprimality exclude the other two values. This is the negative
prime-witness consumer of the combined Euler budget. -/
theorem exists_prime_neg_one_of_twoPole_separation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : 8 ≤ χ.conductor) {x : ℝ}
    (hx : 1 ≤ x) (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap : 0 < twoPoleGammaSeparation χ S x) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  obtain ⟨p, hp, hd, hb, hval⟩ :=
    exists_prime_not_one_of_twoPole_separation χ hquad hne hGRH hm hx S hS hgap
  have hz : χ p ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr
      ((ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hd))
  refine ⟨p, hp, hd, hb, ?_⟩
  rcases hquad (p : ZMod q) with h0 | h1 | hn
  · exact False.elim (hz h0)
  · exact False.elim (hval h1)
  · exact hn

end PseudoPrime.LLS
