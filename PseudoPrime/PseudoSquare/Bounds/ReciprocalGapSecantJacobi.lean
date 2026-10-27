/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapSecantEndpoint
public import PseudoPrime.PseudoSquare.Bounds.ReciprocalGapAmbientJacobi

/-! # Least Jacobi witnesses from variable-gap secant lower bounds -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For odd nonsquare n under GRH, h>0, 64<=Y<=x and selected 4n-coprime
reciprocal support, secant endpoint separation at the canonical conductor yields an odd
prime p<=x with Jacobi(n,p)=-1. Keep both common-factor losses and transfer primitive
character values back to Jacobi. No enumerated principal support is required. -/
theorem exists_odd_prime_jacobi_neg_one_of_reciprocalGap_endpoint_secant {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {h x Y : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x) (C : Finset ℕ)
    (hC : C ⊆ Finset.Ioc 0 ⌊Y⌋₊) (hcopC : ∀ a ∈ C, Nat.Coprime a (4 * n))
    (hgap :
      LLS.PaperStatements.reciprocalGapEndpointSelectedSeparation h
          (NumberTheory.complexQuadraticCharacter n hn).conductor (4 * n) x Y C <
        LLS.PaperStatements.reciprocalGapLogSecant h x *
            (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20 -
              AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum x (4 * n)) /
          Real.sqrt x) :
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
    LLS.PaperStatements.exists_odd_prime_neg_one_of_reciprocalGap_endpoint_secant hh hq hdiv htwo
      hGRH hp hne hquad hx hY hYx C hC hcopC hgap
  have hcp : Nat.Coprime p n := hpc.of_dvd_right (show n ∣ 4 * n from ⟨4, by ring⟩)
  have he :=
    NumberTheory.primitiveQuadraticCharacter_apply_odd_prime hn hprime hodd
      (hprime.coprime_iff_not_dvd.mp hcp)
  simp only [Int.cast_natCast] at he
  have hj : jacobiSym n p = -1 := by exact_mod_cast (he.symm.trans hv)
  exact ⟨p, hprime, hodd, hpx, hcp, hj⟩

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- Under the same odd-nonsquare GRH and secant endpoint conditions, both least
negative and least non-one odd-prime Jacobi witnesses are at most x. Apply leastness
to the constructed negative witness and then inclusion of the witness sets.
This connects the improved analytic criterion to both quadratic witness quantities. -/
theorem primeWitness_cast_le_of_reciprocalGap_endpoint_secant {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {h x Y : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x) (C : Finset ℕ)
    (hC : C ⊆ Finset.Ioc 0 ⌊Y⌋₊) (hcopC : ∀ a ∈ C, Nat.Coprime a (4 * n))
    (hgap :
      LLS.PaperStatements.reciprocalGapEndpointSelectedSeparation h
          (NumberTheory.complexQuadraticCharacter n hn).conductor (4 * n) x Y C <
        LLS.PaperStatements.reciprocalGapLogSecant h x *
            (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20 -
              AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum x (4 * n)) /
          Real.sqrt x) :
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
    exists_odd_prime_jacobi_neg_one_of_reciprocalGap_endpoint_secant hn hns hGRH hh hx hY hYx C hC
      hcopC hgap
  let hneg := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hmem : p ∈ NumberTheory.primeNegOneWitnessSet n := ⟨hprime, hodd, hj⟩
  have hb := (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hneg hmem)).trans hpx
  exact
    ⟨(Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le_primeNegOneWitness n hneg)).trans hb, hb⟩

end PseudoPrime.PseudoSquare
