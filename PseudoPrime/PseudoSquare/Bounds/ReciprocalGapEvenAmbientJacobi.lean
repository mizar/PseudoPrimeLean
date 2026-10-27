/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapEvenAmbientWitness
public import PseudoPrime.NumberTheory.JacobiCharacterArithmetic
public import PseudoPrime.NumberTheory.JacobiWitness.Existence

/-! # Even-parity improvements for least odd-prime Jacobi witnesses -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For every odd nonsquare natural n under GRH and radius x>=1, the explicit ambient
separation at the canonical primitive conductor with exclusion level 4*n gives an odd
prime p<=x coprime to n with Jacobi(n,p)=-1. Build the canonical primitive quadratic
character, retain the additional-nonunit losses and transfer its odd-prime evaluation.
No nonzero-conductor or arithmetic-bridge hypothesis is required from the caller. -/
theorem exists_odd_prime_jacobi_neg_one_of_reciprocalGap_even_ambient {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1 ≤ x) (B₀ B₁ B : Finset ℕ) (hB₀ : ∀ a ∈ B₀, (a : ℝ) ≤ x) (hB₁ : ∀ a ∈ B₁, (a : ℝ) ≤ x)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ a ∈ B, Nat.Coprime a (4 * n)) (lo u : ℕ → ℝ)
    (hlo : ∀ a ∈ B, lo a ≤ ArithmeticFunction.vonMangoldt a)
    (hu : ∀ a ∈ B, ((a : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u a) (hu1 : ∀ a ∈ B, u a ≤ 1)
    (hgap :
      LLS.PaperStatements.reciprocalGapEvenAmbientRationalSeparation
          (NumberTheory.complexQuadraticCharacter n hn).conductor (4 * n) x B₀ B₁ <
        ∑ a ∈ B, (lo a / Real.sqrt x) * ((1 - u a) / (7 / 10 : ℝ))) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p n ∧ jacobiSym n p = -1 := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  let _ : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    ⟨(NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero⟩
  let χ := NumberTheory.primitiveQuadraticCharacter n hn
  have hp : χ.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive (NumberTheory.complexQuadraticCharacter n hn)
  have hquad : χ.IsQuadratic :=
    NumberTheory.isQuadratic_primitiveCharacter (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
  have hne : χ ≠ 1 := NumberTheory.primitiveQuadraticCharacter_ne_one_of_not_square n hn hns
  have hq : 2 ≤ (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (Nat.two_le_iff _).mpr ⟨NeZero.ne _, fun he ↦ hne (DirichletCharacter.level_one' χ he)⟩
  have hdiv := (NumberTheory.complexQuadraticCharacter n hn).conductor_dvd_level
  have htwo : 2 ∣ 4 * n := ⟨2 * n, by ring⟩
  obtain ⟨p, hprime, hodd, hpx, hpc, hv⟩ :=
    LLS.PaperStatements.exists_odd_prime_neg_one_of_reciprocalGap_even_ambient_lower hq hdiv htwo
      hGRH (NumberTheory.primitiveQuadraticCharacter_isEven n hn) hp hne hquad hx B₀ B₁ B hB₀ hB₁ hB
      hcop lo u hlo hu hu1 hgap
  have hcp : Nat.Coprime p n := hpc.of_dvd_right (show n ∣ 4 * n from ⟨4, by ring⟩)
  have he :=
    NumberTheory.primitiveQuadraticCharacter_apply_odd_prime hn hprime hodd
      (hprime.coprime_iff_not_dvd.mp hcp)
  simp only [Int.cast_natCast] at he
  have hj : jacobiSym n p = -1 := by exact_mod_cast (he.symm.trans hv)
  exact ⟨p, hprime, hodd, hpx, hcp, hj⟩

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- Under the parity-sensitive odd-nonsquare, GRH, radius and finite-separation conditions, both
least odd-prime non-one and negative Jacobi witnesses are at most x after real casting.
Extract the actual negative witness, use its leastness and compare both witness sets.
This connects the analytic certificate interface to the public pointwise witness bounds. -/
theorem primeWitness_cast_le_of_reciprocalGap_even_ambient {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (B₀ B₁ B : Finset ℕ) (hB₀ : ∀ a ∈ B₀, (a : ℝ) ≤ x) (hB₁ : ∀ a ∈ B₁, (a : ℝ) ≤ x)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ a ∈ B, Nat.Coprime a (4 * n)) (lo u : ℕ → ℝ)
    (hlo : ∀ a ∈ B, lo a ≤ ArithmeticFunction.vonMangoldt a)
    (hu : ∀ a ∈ B, ((a : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u a) (hu1 : ∀ a ∈ B, u a ≤ 1)
    (hgap :
      LLS.PaperStatements.reciprocalGapEvenAmbientRationalSeparation
          (NumberTheory.complexQuadraticCharacter n hn).conductor (4 * n) x B₀ B₁ <
        ∑ a ∈ B, (lo a / Real.sqrt x) * ((1 - u a) / (7 / 10 : ℝ))) :
    (NumberTheory.primeNeOneWitness n
            (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
              (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
          ℝ) ≤
        x ∧
      (NumberTheory.primeNegOneWitness n
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns) :
          ℝ) ≤
        x := by
  obtain ⟨p, hprime, hodd, hpx, _, hj⟩ :=
    exists_odd_prime_jacobi_neg_one_of_reciprocalGap_even_ambient hn hns hGRH hx B₀ B₁ B hB₀ hB₁ hB
      hcop lo u hlo hu hu1 hgap
  let hneg := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hmem : p ∈ NumberTheory.primeNegOneWitnessSet n := ⟨hprime, hodd, hj⟩
  have hb := (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hneg hmem)).trans hpx
  exact
    ⟨(Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le_primeNegOneWitness n hneg)).trans hb, hb⟩

end PseudoPrime.PseudoSquare
