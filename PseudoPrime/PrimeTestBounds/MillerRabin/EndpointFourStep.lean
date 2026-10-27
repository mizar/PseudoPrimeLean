/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointFourStep
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointEvenPolynomial
/-! # Endpoint witnesses from two and four correction steps -/
@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A positive exact even endpoint gap at radius r>=8 gives a prime rejecting MR below r^2.
For odd composite n>1 under GRH, choose the canonical nonzero instance internally
and convert the existing explicit-power witness into the strong-MR rejection predicate. -/
theorem exists_prime_evenEndpoint {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : 8 ≤ r)
    (hg : 0 < LLS.PaperStatements.fullEndpointEvenExactComparisonGap
      (Real.log n) (2096 / 1831) r (Real.log r)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  obtain ⟨p, hp, hb, hpow, hrest⟩ :=
    exists_prime_reject_of_even_exact_endpoint_gap_pos hn ho hc hGRH hr hg
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩⟩

/-- Under GRH, odd composites with log n>=45/4 have a rejecting prime below C2(log n).
The lower-threshold positive gap and first-to-second radius comparison supply the
generic endpoint consumer. No factorization or subgroup restriction remains. -/
theorem exists_prime_twoStepLower {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 45 / 4 ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ LLS.PaperStatements.fullEndpointEvenTwoStepCutoff (Real.log n) ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_evenEndpoint hn ho hc hGRH _
    (LLS.PaperStatements.endpoint_twoStep_gap hL)
  exact (le_max_left _ _ : (8 : ℝ) ≤
    LLS.PaperStatements.fullEndpointEvenCorrectionFirstRadius (Real.log n)).trans
    (LLS.PaperStatements.correction_second_gt hL).le

/-- Under the two-step lower-threshold assumptions, the least rejecting prime is below C2.
Apply least-prime extraction to the actual prime witness theorem. -/
theorem exists_least_twoStepLower {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 45 / 4 ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ LLS.PaperStatements.fullEndpointEvenTwoStepCutoff (Real.log n) ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject
    (exists_prime_twoStepLower hn ho hc hGRH hL)

/-- Under GRH, odd composites with log n>=45/4 have a rejecting prime below C4(log n).
The clipped third radius and positive fourth-step gap supply the endpoint consumer.
No factorization or subgroup restriction remains. -/
theorem exists_prime_fourStep {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 45 / 4 ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ LLS.PaperStatements.endpointFourStepCutoff (Real.log n) ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_evenEndpoint hn ho hc hGRH _
    (LLS.PaperStatements.endpoint_fourStep_gap hL)
  exact (le_max_left _ _ : (8 : ℝ) ≤
    LLS.PaperStatements.endpointThirdRadius (Real.log n)).trans
    (LLS.PaperStatements.endpoint_fourth_bounds hL).1.le

/-- Under the four-step assumptions, the least rejecting prime is below C4(log n).
Apply least-prime extraction to the actual prime witness theorem. -/
theorem exists_least_fourStep {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 45 / 4 ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ LLS.PaperStatements.endpointFourStepCutoff (Real.log n) ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject
    (exists_prime_fourStep hn ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
