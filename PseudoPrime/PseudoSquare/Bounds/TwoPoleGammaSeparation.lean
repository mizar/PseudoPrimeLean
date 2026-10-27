/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleGammaWitness
public import PseudoPrime.PseudoSquare.Bounds.ExcludedEndpointJacobi

/-! # Jacobi witnesses from two-pole Gamma separation -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For odd nonsquare input under GRH with primitive conductor at least eight,
a positive two-pole separation produces an odd prime negative Jacobi witness
through the ramp cutoff. Convert the original-level character witness by quadratic
reciprocity. The numerical separation remains an explicit analytic premise. -/
theorem exists_odd_prime_jacobi_neg_one_of_twoPole_separation {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hm : 8 ≤ (NumberTheory.complexQuadraticCharacter n hn).conductor) {x : ℝ} (hx : 1 ≤ x)
    (S : Finset ℕ) (hS : ∀ k ∈ S, (k : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap : 0 < LLS.twoPoleGammaSeparation (NumberTheory.complexQuadraticCharacter n hn) S x) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  obtain ⟨p, hp, hd, hb, hv⟩ :=
    LLS.exists_prime_not_one_of_twoPole_separation (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns) hGRH hm hx S hS hgap
  have hw := NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd hv
  exact ⟨p, hw.1, hw.2.1, hb, hw.2.2⟩

/-- Under the same two-pole separation assumptions, bound the least odd negative
Jacobi prime by the ramp cutoff. Apply leastness to the constructed witness.
The nonempty-set argument supplies the existing least-witness definition. -/
theorem primeNegOneWitness_cast_le_of_twoPole_separation {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hm : 8 ≤ (NumberTheory.complexQuadraticCharacter n hn).conductor) {x : ℝ} (hx : 1 ≤ x)
    (S : Finset ℕ) (hS : ∀ k ∈ S, (k : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap : 0 < LLS.twoPoleGammaSeparation (NumberTheory.complexQuadraticCharacter n hn) S x)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_jacobi_neg_one_of_twoPole_separation hn hns hGRH hm hx S hS hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

end PseudoPrime.PseudoSquare
