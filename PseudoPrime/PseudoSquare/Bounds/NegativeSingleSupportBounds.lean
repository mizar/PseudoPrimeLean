/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.NegativeCoprimeCoupledBounds
public import PseudoPrime.LLS.Extensions.EvenCoprimeSingleSupport

/-! # Negative Jacobi witnesses from a cancellation-preserving support budget -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The exact local budget for the level-4n quadratic character at root y.
Sum the combined support terms only where the index shares the level and its
primitive value is not one. This preserves cancellation and excludes zero-value
witnesses from the subsequent negative-witness conclusion. -/
noncomputable def negativeCoprimeSupportCost (n : ℕ) (hn : Odd n) (y : ℝ) : ℝ :=
  ∑
    m ∈
      ((Finset.Ioc 0 ⌊y ^ 2⌋₊).filter (fun m ↦ ¬Nat.Coprime m (4 * n))).filter
        (fun m : ℕ ↦ (NumberTheory.complexQuadraticCharacter n hn).primitiveCharacter m ≠ 1),
    LLS.Extensions.evenCoprimeSupportTerm (NumberTheory.complexQuadraticCharacter n hn) y m

/-- At any root, the negative-witness envelope equals its base plus the
single-support cost. Use exact support transport for the quadratic character.
This connects the reduced finite ledger to the existing witness theorem. -/
theorem negativeCoprimeEnvelope_eq_support_cost (n : ℕ) (hn : Odd n) (y : ℝ) :
    negativeCoprimeEnvelope n hn y =
      LLS.Extensions.evenCoprimeBaseUpper y
          (Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor - Real.log Real.pi)
          (-(179 / 200)) +
        negativeCoprimeSupportCost n hn y := by
  unfold negativeCoprimeEnvelope LLS.Extensions.evenCoprimeUpper
  rw [LLS.Extensions.evenCoprimeLocalCost_eq_filtered_support]
  rfl

/-- Under GRH for odd nonsquare n and root y>=8, an upper bound c for the
single-support cost and a separated base-plus-c gap give an odd prime with
Jacobi value minus one through y squared. Insert the budget into the exact
coprime envelope. The gap remains an explicit quantitative hypothesis. -/
theorem exists_prime_neg_one_witness_of_singleSupportBudget {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y c : ℝ} (hy : (8 : ℝ) ≤ y)
    (hc : negativeCoprimeSupportCost n hn y ≤ c)
    (hgap :
      LLS.Extensions.evenCoprimeBaseUpper y
            (Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor - Real.log Real.pi)
            (-(179 / 200)) +
          c <
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ y ^ 2 ∧ jacobiSym n p = -1 := by
  apply exists_prime_neg_one_witness_of_coupledCoprimeGap hn hns hGRH hy
  rw [negativeCoprimeEnvelope_eq_support_cost]
  linarith only [hc, hgap]

/-- Under the same GRH, root and support-budget hypotheses, the least odd-prime
negative witness is at most y squared. Compare it with the extracted witness.
This supplies a common-endpoint interface for full finite maxima. -/
theorem primeNegOneWitness_cast_le_of_singleSupportBudget {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y c : ℝ} (hy : (8 : ℝ) ≤ y)
    (hc : negativeCoprimeSupportCost n hn y ≤ c)
    (hgap :
      LLS.Extensions.evenCoprimeBaseUpper y
            (Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor - Real.log Real.pi)
            (-(179 / 200)) +
          c <
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2))
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ y ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_prime_neg_one_witness_of_singleSupportBudget hn hns hGRH hy hc hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH at root y>=8, budgets and separated gaps for every admissible
n<=B give QNegOne B<=y^2. Apply the least-witness theorem on the full domain.
Small inputs remain part of the explicit premises; no uniform gap is inferred. -/
theorem QNegOne_le_of_singleSupportBudget {B : ℕ} {y : ℝ} (hy : (8 : ℝ) ≤ y)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (c : ℕ → ℝ)
    (hc : ∀ n : ℕ, (hn : Odd n) → ¬IsSquare n → n ≤ B → negativeCoprimeSupportCost n hn y ≤ c n)
    (hgap :
      ∀ n : ℕ,
        (hn : Odd n) →
          ¬IsSquare n →
            n ≤ B →
            LLS.Extensions.evenCoprimeBaseUpper y
                  (Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor -
                    Real.log Real.pi)
                  (-(179 / 200)) +
                c n <
              AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2)) :
    (QNegOne B : ℝ) ≤ y ^ 2 := by
  apply QNegOne_cast_le_of_forall (sq_nonneg y)
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNegOneWitness_cast_le_of_singleSupportBudget ha.odd ha.not_isSquare hGRH hy
      (hc n ha.odd ha.not_isSquare ha.le) (hgap n ha.odd ha.not_isSquare ha.le)
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

end PseudoPrime.PseudoSquare
