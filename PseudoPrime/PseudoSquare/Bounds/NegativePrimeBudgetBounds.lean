/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.NegativeSingleSupportBounds
public import PseudoPrime.LLS.Extensions.EvenCoprimePrimeBudget

/-! # Negative Jacobi witnesses from prime-factor logarithmic budgets -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- At root y, slope a and exceptional finite support T, bound the quadratic
local cost by a*log(4n) plus positive excesses of its grouped prime costs on T.
This retains primitive-character cancellation on the exceptional support.
The subsequent theorem requires a certified tail bound outside T. -/
noncomputable def negativeCoprimePrimeBudget (n : ℕ) (hn : Odd n) (y : ℝ) (T : Finset ℕ) (a : ℝ) :
    ℝ :=
  a * Real.log (4 * n) +
    ∑ p ∈ T,
      max 0
        (LLS.Extensions.evenCoprimePrimeCost (NumberTheory.complexQuadraticCharacter n hn) y p -
          a * Real.log p)

/-- For odd positive n, nonnegative slope and certified prime tail, the exact
quadratic support cost is at most the logarithmic prime budget.
Use the single-support identity and the prime-factor logarithmic bound.
This supplies the cost premise of the negative-witness criterion. -/
theorem negativeCoprimeSupportCost_le_primeBudget {n : ℕ} (hn : Odd n) (y : ℝ) (T : Finset ℕ)
    {a : ℝ} (ha : 0 ≤ a)
    (htail :
      ∀ p ∈ (4 * n).primeFactors,
        p ∉ T →
          LLS.Extensions.evenCoprimePrimeCost (NumberTheory.complexQuadraticCharacter n hn) y p ≤
            a * Real.log p) :
    negativeCoprimeSupportCost n hn y ≤ negativeCoprimePrimeBudget n hn y T a := by
  have hc :
    negativeCoprimeSupportCost n hn y =
      LLS.Extensions.evenCoprimeLocalCost (NumberTheory.complexQuadraticCharacter n hn) y :=
    (LLS.Extensions.evenCoprimeLocalCost_eq_filtered_support
        (NumberTheory.complexQuadraticCharacter n hn) y).symm
  rw [hc]
  simpa only [negativeCoprimePrimeBudget, Nat.cast_mul, Nat.cast_ofNat] using
    LLS.Extensions.evenCoprimeLocalCost_le_primeBudget
      (Nat.mul_ne_zero (by norm_num only) hn.pos.ne') (NumberTheory.complexQuadraticCharacter n hn)
      y T ha htail

/-- Under GRH for odd nonsquare n and root y>=8, a nonnegative slope, certified
prime tail and separated base-plus-budget gap yield an odd prime with Jacobi
value minus one through y squared. Insert the prime budget into the single-support
witness theorem. The numerical gap remains a premise. -/
theorem exists_prime_neg_one_witness_of_primeBudget {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y a : ℝ} (hy : (8 : ℝ) ≤ y)
    (T : Finset ℕ) (ha : 0 ≤ a)
    (htail :
      ∀ p ∈ (4 * n).primeFactors,
        p ∉ T →
          LLS.Extensions.evenCoprimePrimeCost (NumberTheory.complexQuadraticCharacter n hn) y p ≤
            a * Real.log p)
    (hgap :
      LLS.Extensions.evenCoprimeBaseUpper y
            (Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor - Real.log Real.pi)
            (-(179 / 200)) +
          negativeCoprimePrimeBudget n hn y T a <
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ y ^ 2 ∧ jacobiSym n p = -1 := by
  exact
    exists_prime_neg_one_witness_of_singleSupportBudget hn hns hGRH hy
      (negativeCoprimeSupportCost_le_primeBudget hn y T ha htail) hgap

/-- Under the same prime-budget assumptions, the least odd-prime negative
witness is bounded by y squared. Apply the existing single-support least-witness
interface with the certified logarithmic budget. -/
theorem primeNegOneWitness_cast_le_of_primeBudget {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y a : ℝ} (hy : (8 : ℝ) ≤ y)
    (T : Finset ℕ) (ha : 0 ≤ a)
    (htail :
      ∀ p ∈ (4 * n).primeFactors,
        p ∉ T →
          LLS.Extensions.evenCoprimePrimeCost (NumberTheory.complexQuadraticCharacter n hn) y p ≤
            a * Real.log p)
    (hgap :
      LLS.Extensions.evenCoprimeBaseUpper y
            (Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor - Real.log Real.pi)
            (-(179 / 200)) +
          negativeCoprimePrimeBudget n hn y T a <
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2))
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ y ^ 2 := by
  exact
    primeNegOneWitness_cast_le_of_singleSupportBudget hn hns hGRH hy
      (negativeCoprimeSupportCost_le_primeBudget hn y T ha htail) hgap hw

/-- Under GRH at a common root y>=8, prime tails and separated budgets for all
admissible inputs through B give QNegOne B<=y^2. Pass each input's budget to the
full single-support maximum theorem. No small input is omitted. -/
theorem QNegOne_le_of_primeBudget {B : ℕ} {y a : ℝ} (hy : (8 : ℝ) ≤ y)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (T : Finset ℕ) (ha : 0 ≤ a)
    (htail :
      ∀ n : ℕ,
        (hn : Odd n) →
          ¬IsSquare n →
            n ≤ B →
            ∀ p ∈ (4 * n).primeFactors,
              p ∉ T →
                LLS.Extensions.evenCoprimePrimeCost (NumberTheory.complexQuadraticCharacter n hn) y
                    p ≤
                  a * Real.log p)
    (hgap :
      ∀ n : ℕ,
        (hn : Odd n) →
          ¬IsSquare n →
            n ≤ B →
            LLS.Extensions.evenCoprimeBaseUpper y
                  (Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor -
                    Real.log Real.pi)
                  (-(179 / 200)) +
                negativeCoprimePrimeBudget n hn y T a <
              AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2)) :
    (QNegOne B : ℝ) ≤ y ^ 2 := by
  apply
    QNegOne_le_of_singleSupportBudget hy hGRH
      (fun n ↦ if hn : Odd n then negativeCoprimePrimeBudget n hn y T a else 0)
  · intro n hn hns hnB
    rw [dite_eq_left hn]
    exact negativeCoprimeSupportCost_le_primeBudget hn y T ha (htail n hn hns hnB)
  · intro n hn hns hnB
    rw [dite_eq_left hn]
    exact hgap n hn hns hnB

end PseudoPrime.PseudoSquare
