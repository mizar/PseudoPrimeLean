/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointPointwiseRoot
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointLowPrime

/-! # Least prime witnesses at the pointwise inverse radius -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A nonnegative pointwise level gap still bounds an actual prime witness.
Fix the least witness obtained above y, then use a midpoint below sqrt(p) to rule out p>y^2. -/
theorem exists_prime_of_pointwise_level {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlevel : Real.log n ≤ LLS.PaperStatements.pointwiseLevel y) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have positive {r : ℝ} (hr : y < r) :
    0 < LLS.PaperStatements.endpointPointwiseGap (Real.log n) (2096 / 1831) r (Real.log r) := by
    have hr8 := hy.trans hr.le
    rw [LLS.PaperStatements.pointwiseGap_eq hr8]
    have hm := LLS.PaperStatements.pointwiseLevel_strictMonoOn hy hr8 hr
    exact
      mul_pos (LLS.PaperStatements.fullEndpointEvenGapDenominator_pos hr8)
        (sub_pos.mpr (hlevel.trans_lt hm))
  have hfirst :=
    exists_prime_of_pointwise_gap hn ho hc hGRH (by linarith only [hy] : (2 : ℝ) ≤ y + 1)
      (positive (by linarith only))
  obtain ⟨p, hp, _, hr, hm⟩ := exists_least_prime_reject_of_exists_prime_reject hfirst
  refine ⟨p, hp, ?_, hr⟩
  by_contra hbad
  have hsq : y ^ 2 < (p : ℝ) := lt_of_not_ge hbad
  have hs : y < Real.sqrt p := Real.lt_sqrt_of_sq_lt hsq
  let r : ℝ := (y + Real.sqrt p) / 2
  have hyr : y < r := by
    dsimp only [r]; linarith only [hs]
  have hrs : r < Real.sqrt p := by
    dsimp only [r]; linarith only [hs]
  obtain ⟨q, hq, hb, hqr⟩ :=
    exists_prime_of_pointwise_gap hn ho hc hGRH (by linarith only [hy, hyr] : (2 : ℝ) ≤ r)
      (positive hyr)
  have hsquare : r ^ 2 < (p : ℝ) := by
    have hr0 : 0 ≤ r := by linarith only [hy, hyr]
    have hsqroot := Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
    have hstrict := (sq_lt_sq₀ hr0 (Real.sqrt_nonneg (p : ℝ))).mpr hrs
    linarith only [hstrict, hsqroot]
  exact not_lt.mpr (Nat.cast_le.mpr (hm q hq hqr)) (hb.trans_lt hsquare)

/-- Every odd composite n>1 under GRH has an actual prime witness below the pointwise cutoff. -/
theorem exists_prime_pointwiseRoot {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ LLS.PaperStatements.pointwiseCutoff (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact
    exists_prime_of_pointwise_level hn ho hc hGRH
      (LLS.PaperStatements.pointwiseRadius_spec (Real.log n)).1
      (LLS.PaperStatements.pointwiseRadius_spec (Real.log n)).2.1

/-- The least rejecting prime satisfies the all-input pointwise inverse bound. -/
theorem exists_least_pointwiseRoot {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ LLS.PaperStatements.pointwiseCutoff (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject (exists_prime_pointwiseRoot hn ho hc hGRH)

end PseudoPrime.PrimeTestBounds.MillerRabin
