/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TunedIntervalSelection
public import PseudoPrime.LLS.PaperStatements.EndpointPrime79PlusData
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededSurplus
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointPrime79Plus
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededSurplusBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusBounds

/-! # Public witness bounds from fixed-79 and actual Gaussian surplus -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Preserve the exact small branch and intersect the tuned baseline with the fixed-79 extension
and both Gaussian surplus candidates. Every new candidate keeps its certified guard. -/
noncomputable def nextTunedWitnessEnvelope (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n
  else
    min (tunedWitnessEnvelope n)
      (min (if Real.log n ≤ LLS.PaperStatements.prime79PlusCap then 79 else tunedWitnessEnvelope n)
        (min
          (if 63 ≤ Real.log n then gaussianSeededSurplusFamily (Real.log n)
          else tunedWitnessEnvelope n)
          (if 63 ≤ Real.log n then gaussianSurplusBound (Real.log n) else tunedWitnessEnvelope n)))

/-- The selected numerical expression uses the tuned selection in the same guarded minimum. -/
noncomputable def nextTunedSelectedEnvelope (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n
  else
    min (tunedSelectedEnvelope n)
      (min (if Real.log n ≤ LLS.PaperStatements.prime79PlusCap then 79 else tunedSelectedEnvelope n)
        (min
          (if 63 ≤ Real.log n then gaussianSeededSurplusFamily (Real.log n)
          else tunedSelectedEnvelope n)
          (if 63 ≤ Real.log n then gaussianSurplusBound (Real.log n) else tunedSelectedEnvelope n)))

/-- Round the new guarded witness cutoff to the greatest permitted prime. -/
noncomputable def nextTunedPrimeEnvelope (n : ℕ) : ℝ :=
  primeRound (nextTunedWitnessEnvelope n)

/-- For inputs above one the guarded witness expression equals its selected form. -/
theorem nextTuned_eq_selected {n : ℕ} (hn : 1 < n) :
    nextTunedWitnessEnvelope n = nextTunedSelectedEnvelope n := by
  simp only [nextTunedWitnessEnvelope, nextTunedSelectedEnvelope, tuned_eq_selected hn]

/-- Every natural input below 3000 retains the exact prescribed small cutoff. -/
theorem nextTuned_eq_small {n : ℕ} (hN : n < 3000) :
    nextTunedWitnessEnvelope n = smallIntervalBound n :=
  ite_eq_left hN

/-- The new guarded cutoff never exceeds the preserved tuned baseline at any natural input. -/
theorem nextTuned_le_tuned (n : ℕ) : nextTunedWitnessEnvelope n ≤ tunedWitnessEnvelope n := by
  by_cases hN : n < 3000
  · rw [nextTuned_eq_small hN, tunedWitness_eq_small hN]
  · rw [nextTunedWitnessEnvelope, ite_eq_right hN]
    exact min_le_left _ _

/-- For inputs above one the new selection never exceeds the tuned selection. -/
theorem nextTunedSelected_le_tuned {n : ℕ} (hn : 1 < n) :
    nextTunedSelectedEnvelope n ≤ tunedSelectedEnvelope n := by
  rw [← nextTuned_eq_selected hn, ← tuned_eq_selected hn]
  exact nextTuned_le_tuned n

/-- Prime-preserving rounding retains non-worsening at every natural input. -/
theorem nextTunedPrime_le_tunedPrime (n : ℕ) : nextTunedPrimeEnvelope n ≤ tunedPrimeEnvelope n :=
  primeRound_mono (nextTuned_le_tuned n)

/-- A common lower bound for the old cutoff and each active new candidate bounds their min.
This transfers the same least rejecting prime through all available certificates. -/
theorem nextTuned_lower_of_candidates {n : ℕ} (hN : 3000 ≤ n) {C : ℝ}
    (hB : C ≤ tunedWitnessEnvelope n)
    (hF : Real.log n ≤ LLS.PaperStatements.prime79PlusCap → C ≤ 79)
    (hS : 63 ≤ Real.log n → C ≤ gaussianSeededSurplusFamily (Real.log n))
    (hG : 63 ≤ Real.log n → C ≤ gaussianSurplusBound (Real.log n)) :
    C ≤ nextTunedWitnessEnvelope n := by
  rw [nextTunedWitnessEnvelope, ite_eq_right (not_lt.mpr hN)]
  apply le_min hB
  apply le_min
  · by_cases h : Real.log n ≤ LLS.PaperStatements.prime79PlusCap
    · exact (hF h).trans_eq (ite_eq_left h).symm
    · exact hB.trans_eq (ite_eq_right h).symm
  · apply le_min
    · by_cases h : 63 ≤ Real.log n
      · exact (hS h).trans_eq (ite_eq_left h).symm
      · exact hB.trans_eq (ite_eq_right h).symm
    · by_cases h : 63 ≤ Real.log n
      · exact (hG h).trans_eq (ite_eq_left h).symm
      · exact hB.trans_eq (ite_eq_right h).symm

/-- At the fixed-79 entrance the new cutoff is at most 79 above the small branch. -/
theorem nextTuned_le79 {n : ℕ} (hN : 3000 ≤ n)
    (hL : Real.log n ≤ LLS.PaperStatements.prime79PlusCap) : nextTunedWitnessEnvelope n ≤ 79 := by
  rw [nextTunedWitnessEnvelope, ite_eq_right (not_lt.mpr hN)]
  exact (min_le_right _ _).trans ((min_le_left _ _).trans (le_of_eq (ite_eq_left hL)))

/-- Above scale 63 the new cutoff is below either certified surplus seeded profile. -/
theorem nextTuned_le_seeded {n : ℕ} (f : Bool) (hL : 63 ≤ Real.log n) :
    nextTunedWitnessEnvelope n ≤ gaussianSeededSurplusBound f (Real.log n) := by
  rw [nextTunedWitnessEnvelope, ite_eq_right (not_lt.mpr (large_of_log63 hL))]
  have h :
    min (tunedWitnessEnvelope n)
        (min
          (if Real.log n ≤ LLS.PaperStatements.prime79PlusCap then 79 else tunedWitnessEnvelope n)
          (min
            (if 63 ≤ Real.log n then gaussianSeededSurplusFamily (Real.log n)
            else tunedWitnessEnvelope n)
            (if 63 ≤ Real.log n then gaussianSurplusBound (Real.log n)
            else tunedWitnessEnvelope n))) ≤
      gaussianSeededSurplusFamily (Real.log n) :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_left _ _).trans (le_of_eq (ite_eq_left hL))))
  cases f
  · exact h.trans (min_le_left _ _)
  · exact h.trans (min_le_right _ _)

/-- Under GRH each odd composite above one has a least rejecting prime below the new min.
Transfer the actual candidate bounds by leastness, preserving the exact small branch. -/
theorem exists_least_nextTunedEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ nextTunedWitnessEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_tunedEnvelope hn ho hc hGRH
  have transfer {C : ℝ}
    (hw : ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ C ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n)) :
    (p : ℝ) ≤ C := by
    obtain ⟨q, hq, hqb, hqr⟩ := hw
    exact (Nat.cast_le.mpr (hm q hq hqr)).trans hqb
  by_cases hN : n < 3000
  · refine ⟨p, hp, hr, ?_, hm⟩
    rw [nextTuned_eq_small hN, ← tunedWitness_eq_small hN]
    exact hb
  · exact
      ⟨p, hp, hr,
        nextTuned_lower_of_candidates (le_of_not_gt hN) hb
          (fun hL ↦ transfer (exists_prime_endpoint79Plus hn ho hc hGRH hL))
          (fun hL ↦ transfer (exists_prime_seededSurplusFamily ho hc hGRH hL))
          (fun hL ↦ transfer (exists_prime_gaussianSurplus ho hc hGRH hL)),
        hm⟩

/-- Under GRH the guarded new cutoff contains an actual prime rejecting strong MR. -/
theorem exists_prime_nextTunedEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ nextTunedWitnessEnvelope n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_nextTunedEnvelope hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩

/-- The exact selected expression preserves the same least rejecting prime under GRH. -/
theorem exists_least_nextTunedSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ nextTunedSelectedEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  rw [← nextTuned_eq_selected hn]
  exact exists_least_nextTunedEnvelope hn ho hc hGRH

/-- Under GRH the new selected cutoff contains an actual rejecting prime. -/
theorem exists_prime_nextTunedSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ nextTunedSelectedEnvelope n ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rw [← nextTuned_eq_selected hn]
  exact exists_prime_nextTunedEnvelope hn ho hc hGRH

/-- Prime-preserving rounding retains the same least rejecting prime under GRH. -/
theorem exists_least_nextTunedPrimeEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ nextTunedPrimeEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_nextTunedEnvelope hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

/-- Under GRH the new rounded cutoff contains an actual rejecting prime. -/
theorem exists_prime_nextTunedPrimeEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ nextTunedPrimeEnvelope n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_nextTunedPrimeEnvelope hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
