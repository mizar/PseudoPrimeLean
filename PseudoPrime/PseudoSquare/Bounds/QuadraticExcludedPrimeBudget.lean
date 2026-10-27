/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.QuadraticExcludedPrimeBudget
public import PseudoPrime.PseudoSquare.Bounds.QuadraticExcludedEndpoint

/-! # Jacobi witness bounds from retained prime-factor excess budgets -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

open AnalyticNumberTheory.Arithmetic in
/-- For odd nonsquare n under GRH, x>=64 and a>=0, suppose prime costs outside
finite T obey the logarithmic tail bound and the resulting scalar separation is
negative. Then an odd negative Jacobi prime exists below x and is coprime to n.
Apply the structural prime-budget bound before the established Jacobi criterion. -/
theorem exists_odd_prime_jacobi_neg_one_of_quadratic_prime_budget {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 64 ≤ x) (T : Finset ℕ) {a : ℝ} (ha : 0 ≤ a)
    (htail :
      ∀ p ∈ (4 * n).primeFactors,
        p ∉ T →
          quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
              (LLS.PaperStatements.excludedEndpointWeight x) p ≤
            a * Real.log p)
    (hsep :
      LLS.PaperStatements.oddEndpointTwoCostLimit
            (NumberTheory.complexQuadraticCharacter n hn).conductor x x 0 0 +
          a * Real.log (4 * n : ℕ) +
          ∑ p ∈ T,
            max 0
              (quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
                  (LLS.PaperStatements.excludedEndpointWeight x) p -
                a * Real.log p) <
        0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p n ∧ jacobiSym n p = -1 := by
  have hx0 : 0 ≤ x := le_trans (by norm_num only : (0 : ℝ) ≤ 64) hx
  have hN : 4 * n ≠ 0 := Nat.mul_ne_zero (by norm_num only) hn.pos.ne'
  have hb :=
    quadraticExcludedBudget_le_primeBudget hN
      (NumberTheory.complexQuadraticCharacter n hn).conductor hx0
      (LLS.PaperStatements.excludedEndpointWeight x)
      (fun _ h ↦ LLS.PaperStatements.excludedEndpointWeight_eq_zero_of_not_primePow x h) T ha htail
  apply exists_odd_prime_jacobi_neg_one_of_quadratic_excluded_budget hn hns hGRH hx
  linarith only [hb, hsep]

open AnalyticNumberTheory.Arithmetic in
/-- With the same GRH, odd nonsquare and prime-budget hypotheses, the least odd
negative Jacobi prime is at most x. The nonempty-set input supplies the existing
least-witness definition; apply leastness to the prime constructed by the criterion. -/
theorem primeNegOneWitness_cast_le_of_quadratic_prime_budget {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 64 ≤ x) (T : Finset ℕ) {a : ℝ} (ha : 0 ≤ a)
    (htail :
      ∀ p ∈ (4 * n).primeFactors,
        p ∉ T →
          quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
              (LLS.PaperStatements.excludedEndpointWeight x) p ≤
            a * Real.log p)
    (hsep :
      LLS.PaperStatements.oddEndpointTwoCostLimit
            (NumberTheory.complexQuadraticCharacter n hn).conductor x x 0 0 +
          a * Real.log (4 * n : ℕ) +
          ∑ p ∈ T,
            max 0
              (quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
                  (LLS.PaperStatements.excludedEndpointWeight x) p -
                a * Real.log p) <
        0)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ x := by
  obtain ⟨p, hp, ho, hpx, _, hv⟩ :=
    exists_odd_prime_jacobi_neg_one_of_quadratic_prime_budget hn hns hGRH hx T ha htail hsep
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

open AnalyticNumberTheory.Arithmetic in
/-- Under GRH, x>=64 and a>=0, suppose every admissible n<=B satisfies the same
prime-tail bound and its exceptional-prime budget is at most Z. If the zero-cost
endpoint expression at level 4*B plus Z is negative, QNegOne(B)<=x. Bound each
structural budget and use the existing uniform endpoint theorem. Numerical
certification of the rate, excesses and separation remains an explicit input. -/
theorem QNegOne_cast_le_of_quadratic_prime_budget {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Z a : ℝ} (hx : 64 ≤ x)
    (ha : 0 ≤ a) (T : Finset ℕ)
    (htail :
      ∀ n ∈ NumberTheory.admissibleFinset B,
        ∀ hn : Odd n,
          ∀ p ∈ (4 * n).primeFactors,
            p ∉ T →
              quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
                  (LLS.PaperStatements.excludedEndpointWeight x) p ≤
                a * Real.log p)
    (hbudget :
      ∀ n ∈ NumberTheory.admissibleFinset B,
        ∀ hn : Odd n,
          a * Real.log (4 * n : ℕ) +
              ∑ p ∈ T,
                max 0
                  (quadraticExcludedPrimeCost
                      (NumberTheory.complexQuadraticCharacter n hn).conductor x
                      (LLS.PaperStatements.excludedEndpointWeight x) p -
                    a * Real.log p) ≤
            Z)
    (hsep : LLS.PaperStatements.oddEndpointTwoCostLimit (4 * B) x x 0 0 + Z < 0) :
    (QNegOne B : ℝ) ≤ x := by
  apply QNegOne_cast_le_of_quadratic_excluded_budget hGRH hx _ hsep
  intro n hn ho
  have hx0 : 0 ≤ x := le_trans (by norm_num only : (0 : ℝ) ≤ 64) hx
  have hN : 4 * n ≠ 0 := Nat.mul_ne_zero (by norm_num only) ho.pos.ne'
  exact
    (quadraticExcludedBudget_le_primeBudget hN
          (NumberTheory.complexQuadraticCharacter n ho).conductor hx0
          (LLS.PaperStatements.excludedEndpointWeight x)
          (fun _ h ↦ LLS.PaperStatements.excludedEndpointWeight_eq_zero_of_not_primePow x h) T ha
          (htail n hn ho)).trans
      (hbudget n hn ho)

open AnalyticNumberTheory.Arithmetic in
/-- Under the same uniform prime-budget hypotheses, QNeOne(B)<=x follows from
the negative-witness finite maximum. Use QNeOne<=QNegOne and the new prime-budget
criterion. This does not identify the least non-one and negative witnesses. -/
theorem QNeOne_cast_le_of_quadratic_prime_budget {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Z a : ℝ} (hx : 64 ≤ x)
    (ha : 0 ≤ a) (T : Finset ℕ)
    (htail :
      ∀ n ∈ NumberTheory.admissibleFinset B,
        ∀ hn : Odd n,
          ∀ p ∈ (4 * n).primeFactors,
            p ∉ T →
              quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
                  (LLS.PaperStatements.excludedEndpointWeight x) p ≤
                a * Real.log p)
    (hbudget :
      ∀ n ∈ NumberTheory.admissibleFinset B,
        ∀ hn : Odd n,
          a * Real.log (4 * n : ℕ) +
              ∑ p ∈ T,
                max 0
                  (quadraticExcludedPrimeCost
                      (NumberTheory.complexQuadraticCharacter n hn).conductor x
                      (LLS.PaperStatements.excludedEndpointWeight x) p -
                    a * Real.log p) ≤
            Z)
    (hsep : LLS.PaperStatements.oddEndpointTwoCostLimit (4 * B) x x 0 0 + Z < 0) :
    (QNeOne B : ℝ) ≤ x := by
  exact
    (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans
      (QNegOne_cast_le_of_quadratic_prime_budget hGRH hx ha T htail hbudget hsep)

end PseudoPrime.PseudoSquare
