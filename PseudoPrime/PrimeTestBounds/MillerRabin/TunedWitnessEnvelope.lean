/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TunedGuards
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointTunedEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianTunedBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededTuned
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededTunedBounds

/-! # Tuned public witness envelope preserving the sharp baseline -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Preserve the small branch and intersect current sharp with all newly certified candidates.
Each analytic or triangular candidate retains its own proved entrance. -/
noncomputable def tunedWitnessEnvelope (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n
  else
    sharpGuardMin (Real.log n) (tunedFiniteWitness n) (gaussianTunedFamily (Real.log n))
      (min (gaussianSeededTunedBound false (Real.log n))
        (gaussianSeededTunedBound true (Real.log n)))
      (tunedHighMin (Real.log n) (tunedFiniteWitness n))

/-- Use the fourteen exact finite intervals and the selected analytic guard assembly.
This function is numerically equal to the guarded witness minimum for inputs above one. -/
noncomputable def tunedSelectedEnvelope (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n
  else
    sharpGuardSelected (Real.log n) (tunedFiniteSelected n) (gaussianTunedFamily (Real.log n))
      (min (gaussianSeededTunedBound false (Real.log n))
        (gaussianSeededTunedBound true (Real.log n)))
      (tunedHighMin (Real.log n) (tunedFiniteSelected n))

/-- Round the tuned witness cutoff down to the greatest allowed prime. -/
noncomputable def tunedPrimeEnvelope (n : ℕ) : ℝ :=
  primeRound (tunedWitnessEnvelope n)

/-- For inputs above one the guarded minimum equals the exact selected expression. -/
theorem tuned_eq_selected {n : ℕ} (hn : 1 < n) :
    tunedWitnessEnvelope n = tunedSelectedEnvelope n := by
  simp only [tunedWitnessEnvelope, tunedSelectedEnvelope, tunedFinite_eq_selected hn,
    sharpGuardMin_eq_selected]

/-- All natural inputs below 3000 retain the prescribed small witness value. -/
theorem tunedWitness_eq_small {n : ℕ} (hN : n < 3000) :
    tunedWitnessEnvelope n = smallIntervalBound n :=
  ite_eq_left hN

/-- The tuned public cutoff never exceeds its finite-candidate base. -/
theorem tunedWitness_le_finite (n : ℕ) : tunedWitnessEnvelope n ≤ tunedFiniteWitness n := by
  by_cases hN : n < 3000
  · rw [tunedWitness_eq_small hN, tunedFiniteWitness_eq_small hN]
  · rw [tunedWitnessEnvelope, ite_eq_right hN]
    exact min_le_left _ _

/-- For inputs above one the tuned witness cutoff never exceeds current sharp. -/
theorem tunedWitness_le_sharp {n : ℕ} (hn : 1 < n) :
    tunedWitnessEnvelope n ≤ sharpWitnessEnvelope n :=
  (tunedWitness_le_finite n).trans (tunedFiniteWitness_le_sharp hn)

/-- A common lower bound of the finite base and every active new candidate bounds the public min.
This is the interface for transferring the same least prime across all candidates. -/
theorem tuned_lower_of_candidates {n : ℕ} (hN : 3000 ≤ n) {C : ℝ} (hB : C ≤ tunedFiniteWitness n)
    (hG : 63 ≤ Real.log n → C ≤ gaussianTunedFamily (Real.log n))
    (hS : ∀ f : Bool, 63 ≤ Real.log n → C ≤ gaussianSeededTunedBound f (Real.log n))
    (hH :
      ∀ i : Fin 7,
        (triangularTunedProfile i).T ≤ Real.log n →
          C ≤ (triangularTunedProfile i).C * Real.log n ^ 2) :
    C ≤ tunedWitnessEnvelope n := by
  rw [tunedWitnessEnvelope, ite_eq_right (not_lt.mpr hN)]
  exact sharpGuard_lower hB hG (fun h ↦ le_min (hS false h) (hS true h)) (tunedHigh_lower hB hH)

/-- Under GRH every odd composite above one has the same least rejecting prime below all active
new cutoffs. Minimality transfers the separately certified actual witness bounds to the min. -/
theorem exists_least_tunedEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ tunedWitnessEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_tunedFiniteWitness hn ho hc hGRH
  have transfer {C : ℝ}
    (hw : ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ C ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n)) :
    (p : ℝ) ≤ C := by
    obtain ⟨q, hq, hqb, hqr⟩ := hw
    exact (Nat.cast_le.mpr (hm q hq hqr)).trans hqb
  by_cases hN : n < 3000
  · exact
      ⟨p, hp, hr, by
        rw [tunedWitness_eq_small hN, ← tunedFiniteWitness_eq_small hN]
        exact hb, hm⟩
  · exact
      ⟨p, hp, hr,
        tuned_lower_of_candidates (le_of_not_gt hN) hb
          (fun hL ↦ transfer (exists_prime_gaussianTunedFamily ho hc hGRH hL))
          (fun f hL ↦ transfer (exists_prime_seededTuned f ho hc hGRH hL))
          (fun i hL ↦ transfer (exists_prime_triangularTunedProfile i hn ho hc hGRH hL)),
        hm⟩

/-- Under GRH the tuned witness cutoff contains an actual prime rejecting strong MR. -/
theorem exists_prime_tunedEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ tunedWitnessEnvelope n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_tunedEnvelope hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩

/-- Prime-preserving rounding keeps the same least rejecting prime
under the tuned rounded cutoff. -/
theorem exists_least_tunedPrimeEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ tunedPrimeEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_tunedEnvelope hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
