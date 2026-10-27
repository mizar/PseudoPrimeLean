/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GeneralGammaRampComparison
public import PseudoPrime.LLS.TwoPoleGammaWitness

/-! # General-character witnesses from paired Euler two-pole Gamma bounds -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For an arbitrary character, retain the exact excluded-support defect in the
two-pole Gamma arithmetic budget. Use conductor mass, a sharp left integral and an
ambient pole modulus max(20000,q); add the actual local correction. This covers
small primitive conductors without assuming quadraticity. -/
noncomputable def generalTwoPoleGammaUpper {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset ℕ)
    (x : ℝ) : ℝ :=
  Real.log χ.conductor / 2 + 419 / 50 -
      2 *
        (∑ n ∈ S,
          AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n) +
    AnalyticNumberTheory.Arithmetic.excludedCharacterDefect χ.primitiveCharacter q S
      (AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) +
    64 / 9 +
    ((7 / 6 : ℝ) * Real.log (max 20000 q : ℕ) + 4) / Real.sqrt x +
    x ^ (-9 / 16 : ℝ) * ((3 / 2) * (Real.log χ.conductor + 28) + 1) +
    gammaQuadraticLocalCorrection χ x

/-- Twice the principal ramp lower bound minus the principal Gamma upper bound and
the general two-pole arithmetic budget. Positivity implies a prime character
witness. This scalar criterion retains exact finite character values and losses. -/
noncomputable def generalTwoPoleGammaSeparation {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset ℕ)
    (x : ℝ) : ℝ :=
  2 *
      ((∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x -
        gammaRampPairedErrorNumerator x / Real.sqrt x) -
    (Real.sqrt x +
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x) -
    generalTwoPoleGammaUpper χ S x

open AnalyticNumberTheory.Arithmetic in
/-- For a nonprincipal complex character under GRH, scale at least one and finite
support below the cutoff, eligible-prime triviality gives the general two-pole
arithmetic bound. Transfer to the primitive source and use the exact weighted
defect identity. No conductor-eight or quadraticity assumption is needed. -/
theorem gamma_primitive_sum_add_local_le_generalTwoPole {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re +
        gammaQuadraticLocalCorrection χ x ≤
      generalTwoPoleGammaUpper χ S x := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := primitiveCharacter_ne_one χ hne
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hC :=
    PaperStatements.gamma_primitive_sum_re_le_twoPole (le_max_left 20000 q) hm
      (hmq.trans (le_max_right 20000 q)) hGRH hp hnp (inv_ne_one.mpr hnp) hx S S
  have ht :
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → Nat.Coprime p q → χ.primitiveCharacter p = 1 :=
    fun p hprime hpb hcop ↦
    PaperStatements.primitiveCharacter_apply_one_of_apply_one χ
      (hsmall p hprime (hprime.coprime_iff_not_dvd.mp hcop) hpb)
  have he := paired_euler_prefixes_eq_weight χ.primitiveCharacter (5 / 4) (11 / 4) (3 / 4) S
  have hd :=
    paired_weighted_sum_eq_of_ambient_trivial χ.primitiveCharacter S
      (pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) hS
      (fun n _ hn ↦ pairedEulerPrefixWeight_eq_zero_of_mangoldt_eq_zero _ _ _ hn) ht
  dsimp only [generalTwoPoleGammaUpper]
  linarith only [hC, he, hd]

/-- For a nonprincipal complex character under GRH, positivity of the general
two-pole separation excludes triviality on every eligible prime through the cutoff.
Combine the general ramp comparison with the sharp arithmetic bound. This is the
analytic contradiction for nonquadratic character and subgroup witnesses. -/
theorem gamma_prime_trivial_false_generalTwoPole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1 ≤ x) (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap : 0 < generalTwoPoleGammaSeparation χ S x) :
    ¬(∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  intro hsmall
  have hC := gamma_primitive_sum_add_local_le_generalTwoPole χ hne hGRH hx S hS hsmall
  have hT := gamma_ramp_sum_lower_paired hGRH.riemann hx
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann hx
  have hN := gamma_ramp_no_witness_comparison_general χ (zero_lt_one.trans_le hx) hsmall
  dsimp only [generalTwoPoleGammaSeparation] at hgap
  linarith only [hC, hT, hP, hN, hgap]

/-- For a nonprincipal complex character under GRH and positive general two-pole
separation, a prime through the cutoff does not divide the level and has character
value different from one. Negate prime triviality. This is the common witness API
for proper subgroups and Miller-Rabin pass containment. -/
theorem exists_prime_not_one_of_generalTwoPole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1 ≤ x) (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap : 0 < generalTwoPoleGammaSeparation χ S x) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
  classical
  by_contra h
  apply gamma_prime_trivial_false_generalTwoPole χ hne hGRH hx S hS hgap
  intro p hp hd hb
  apply Classical.byContradiction
  intro hn
  exact h ⟨p, hp, hd, hb, hn⟩

end PseudoPrime.LLS
