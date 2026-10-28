/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LowPrimeEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointPointwiseRoot
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointPointwiseSteps
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMR1000Comparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaReflectedEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMRSeededComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularEarlyBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularNextBounds
public import PseudoPrime.LLS.EndpointStepComparison

/-! # The next all-input GRH prime witness envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The minimum of the low-prime base and all certified next candidates.
Every conditional candidate uses its proved domain and otherwise returns the base. -/
noncomputable def nextWitnessEnvelope (n : ℕ) : ℝ :=
  let L := Real.log n
  let B := lowPrimeEnvelope n
  min B <|
    min (LLS.PaperStatements.pointwiseCutoff L) <|
    min (if 63 ≤ L then Analysis.gaussian1000Bound L else B) <|
    min (if 100 ≤ L then gammaReflectedBound L else B) <|
    min (if 63 ≤ L then Analysis.gaussianSeededSelected L else B) <|
    min (if L ≤ 11509 / 1000 then 61 else B) <|
    min (if L ≤ 1179 / 100 then 67 else B) <|
    min (if L ≤ 1193 / 100 then 71 else B) <|
    min (if L ≤ 12337 / 1000 then 73 else B) <|
    min (if 1500000000000 ≤ L then (282924 / 1000000) * L ^ 2 else B)
      (if 2000000000000 ≤ L then (2827 / 10000) * L ^ 2 else B)

/-- For all natural inputs the next envelope is no larger than the low-prime base. -/
theorem nextWitnessEnvelope_le_low (n : ℕ) : nextWitnessEnvelope n ≤ lowPrimeEnvelope n := by
  exact min_le_left _ _

/-- For all natural inputs the next envelope preserves the previous proved upper bound. -/
theorem nextWitnessEnvelope_le_improved (n : ℕ) :
    nextWitnessEnvelope n ≤ improvedWitnessEnvelope n := by
  exact (nextWitnessEnvelope_le_low n).trans (lowPrimeEnvelope_le_improved n)

/-- The next envelope is bounded by the certified pointwise candidate. -/
theorem next_le_pointwise {n : ℕ} :
    nextWitnessEnvelope n ≤ LLS.PaperStatements.pointwiseCutoff (Real.log n) := by
  have hb : nextWitnessEnvelope n ≤ LLS.PaperStatements.pointwiseCutoff (Real.log n) := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  exact hb

/-- The next envelope is bounded by the certified gaussian1000 candidate. -/
theorem next_le_gaussian1000 {n : ℕ} (h : 63 ≤ Real.log n) :
    nextWitnessEnvelope n ≤ Analysis.gaussian1000Bound (Real.log n) := by
  have hb :
    nextWitnessEnvelope n ≤
      (if 63 ≤ Real.log n then Analysis.gaussian1000Bound (Real.log n)
      else lowPrimeEnvelope n) := by
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  simpa only [ite_eq_left h] using hb

/-- The next envelope is bounded by the certified reflected candidate. -/
theorem next_le_reflected {n : ℕ} (h : 100 ≤ Real.log n) :
    nextWitnessEnvelope n ≤ gammaReflectedBound (Real.log n) := by
  have hb :
    nextWitnessEnvelope n ≤
      (if 100 ≤ Real.log n then gammaReflectedBound (Real.log n) else lowPrimeEnvelope n) := by
    exact
      (min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  simpa only [ite_eq_left h] using hb

/-- The next envelope is bounded by the certified seeded candidate. -/
theorem next_le_seeded {n : ℕ} (h : 63 ≤ Real.log n) :
    nextWitnessEnvelope n ≤ Analysis.gaussianSeededSelected (Real.log n) := by
  have hb :
    nextWitnessEnvelope n ≤
      (if 63 ≤ Real.log n then Analysis.gaussianSeededSelected (Real.log n)
      else lowPrimeEnvelope n) := by
    exact
      (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  simpa only [ite_eq_left h] using hb

/-- The next envelope is bounded by the certified fixed61 candidate. -/
theorem next_le_fixed61 {n : ℕ} (h : Real.log n ≤ 11509 / 1000) :
    nextWitnessEnvelope n ≤ (61 : ℝ) := by
  have hb :
    nextWitnessEnvelope n ≤
      (if Real.log n ≤ 11509 / 1000 then (61 : ℝ) else lowPrimeEnvelope n) := by
    exact
      (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  simpa only [ite_eq_left h] using hb

/-- The next envelope is bounded by the certified fixed67 candidate. -/
theorem next_le_fixed67 {n : ℕ} (h : Real.log n ≤ 1179 / 100) :
    nextWitnessEnvelope n ≤ (67 : ℝ) := by
  have hb :
    nextWitnessEnvelope n ≤ (if Real.log n ≤ 1179 / 100 then (67 : ℝ) else lowPrimeEnvelope n) := by
    exact
      (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
  simpa only [ite_eq_left h] using hb

/-- The next envelope is bounded by the certified fixed71 candidate. -/
theorem next_le_fixed71 {n : ℕ} (h : Real.log n ≤ 1193 / 100) :
    nextWitnessEnvelope n ≤ (71 : ℝ) := by
  have hb :
    nextWitnessEnvelope n ≤ (if Real.log n ≤ 1193 / 100 then (71 : ℝ) else lowPrimeEnvelope n) := by
    exact
      (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))))
  simpa only [ite_eq_left h] using hb

/-- The next envelope is bounded by the certified fixed73 candidate. -/
theorem next_le_fixed73 {n : ℕ} (h : Real.log n ≤ 12337 / 1000) :
    nextWitnessEnvelope n ≤ (73 : ℝ) := by
  have hb :
    nextWitnessEnvelope n ≤
      (if Real.log n ≤ 12337 / 1000 then (73 : ℝ) else lowPrimeEnvelope n) := by
    exact
      (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans
                  ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))))
  simpa only [ite_eq_left h] using hb

/-- The next envelope is bounded by the certified early candidate. -/
theorem next_le_early {n : ℕ} (h : 1500000000000 ≤ Real.log n) :
    nextWitnessEnvelope n ≤ (282924 / 1000000 : ℝ) * Real.log n ^ 2 := by
  have hb :
    nextWitnessEnvelope n ≤
      (if 1500000000000 ≤ Real.log n then (282924 / 1000000 : ℝ) * Real.log n ^ 2
      else lowPrimeEnvelope n) := by
    exact
      (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans
                  ((min_le_right _ _).trans
                    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))))))
  simpa only [ite_eq_left h] using hb

/-- The next envelope is bounded by the certified triangular candidate. -/
theorem next_le_triangular {n : ℕ} (h : 2000000000000 ≤ Real.log n) :
    nextWitnessEnvelope n ≤ (2827 / 10000 : ℝ) * Real.log n ^ 2 := by
  have hb :
    nextWitnessEnvelope n ≤
      (if 2000000000000 ≤ Real.log n then (2827 / 10000 : ℝ) * Real.log n ^ 2
      else lowPrimeEnvelope n) := by
    exact
      (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans
                  ((min_le_right _ _).trans
                    ((min_le_right _ _).trans
                      ((min_le_right _ _).trans ((min_le_right _ _).trans (le_refl _))))))))))
  simpa only [ite_eq_left h] using hb

/-- Every odd composite n>1 under GRH has one least rejecting prime satisfying all
valid next candidates. Transfer their witnesses by minimality before forming the minimum. -/
theorem exists_least_nextEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ nextWitnessEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_lowPrimeEnvelope hn ho hc hGRH
  have transfer {C : ℝ}
    (h : ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ C ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n)) :
    (p : ℝ) ≤ C := by
    obtain ⟨q, hq, hqb, hqr⟩ := h
    exact (Nat.cast_le.mpr (hm q hq hqr)).trans hqb
  have h_pointwise : (p : ℝ) ≤ LLS.PaperStatements.pointwiseCutoff (Real.log n) := by
    exact transfer (exists_prime_pointwiseRoot hn ho hc hGRH)
  have h_gaussian1000 :
    (p : ℝ) ≤
      (if 63 ≤ Real.log n then Analysis.gaussian1000Bound (Real.log n)
      else lowPrimeEnvelope n) := by
    by_cases h : 63 ≤ Real.log n
    · rw [ite_eq_left h]
      exact transfer (exists_prime_gaussian1000 ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h_reflected :
    (p : ℝ) ≤
      (if 100 ≤ Real.log n then gammaReflectedBound (Real.log n) else lowPrimeEnvelope n) := by
    by_cases h : 100 ≤ Real.log n
    · rw [ite_eq_left h]
      exact transfer (exists_prime_gammaReflected hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h_seeded :
    (p : ℝ) ≤
      (if 63 ≤ Real.log n then Analysis.gaussianSeededSelected (Real.log n)
      else lowPrimeEnvelope n) := by
    by_cases h : 63 ≤ Real.log n
    · rw [ite_eq_left h]
      rw [← Analysis.gaussianSeeded_min_eq_selected h]
      exact transfer (exists_prime_gaussianSeededEnvelope ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h_fixed61 :
    (p : ℝ) ≤ (if Real.log n ≤ 11509 / 1000 then (61 : ℝ) else lowPrimeEnvelope n) := by
    by_cases h : Real.log n ≤ 11509 / 1000
    · rw [ite_eq_left h]
      exact transfer (exists_prime_pointwiseStep61 hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h_fixed67 :
    (p : ℝ) ≤ (if Real.log n ≤ 1179 / 100 then (67 : ℝ) else lowPrimeEnvelope n) := by
    by_cases h : Real.log n ≤ 1179 / 100
    · rw [ite_eq_left h]
      exact transfer (exists_prime_pointwiseStep67 hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h_fixed71 :
    (p : ℝ) ≤ (if Real.log n ≤ 1193 / 100 then (71 : ℝ) else lowPrimeEnvelope n) := by
    by_cases h : Real.log n ≤ 1193 / 100
    · rw [ite_eq_left h]
      exact transfer (exists_prime_pointwiseStep71 hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h_fixed73 :
    (p : ℝ) ≤ (if Real.log n ≤ 12337 / 1000 then (73 : ℝ) else lowPrimeEnvelope n) := by
    by_cases h : Real.log n ≤ 12337 / 1000
    · rw [ite_eq_left h]
      exact transfer (exists_prime_pointwiseStep73 hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h_early :
    (p : ℝ) ≤
      (if 1500000000000 ≤ Real.log n then (282924 / 1000000 : ℝ) * Real.log n ^ 2
      else lowPrimeEnvelope n) := by
    by_cases h : 1500000000000 ≤ Real.log n
    · rw [ite_eq_left h]
      exact transfer (exists_prime_triangularEarly hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h_triangular :
    (p : ℝ) ≤
      (if 2000000000000 ≤ Real.log n then (2827 / 10000 : ℝ) * Real.log n ^ 2
      else lowPrimeEnvelope n) := by
    by_cases h : 2000000000000 ≤ Real.log n
    · rw [ite_eq_left h]
      exact transfer (exists_prime_triangularNext hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  exact
    ⟨p, hp, hr,
      le_min hb
        (le_min h_pointwise
          (le_min h_gaussian1000
            (le_min h_reflected
              (le_min h_seeded
                (le_min h_fixed61
                  (le_min h_fixed67
                    (le_min h_fixed71 (le_min h_fixed73 (le_min h_early h_triangular))))))))),
      hm⟩

/-- Every odd composite n>1 under GRH has an actual prime witness within the next envelope. -/
theorem exists_prime_nextEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ nextWitnessEnvelope n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_nextEnvelope hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
