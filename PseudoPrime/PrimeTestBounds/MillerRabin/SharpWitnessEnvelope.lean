/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SharpGuards
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFiniteEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLowFloorBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededSharpOrder
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularProfileBounds

/-! # Sharp public witness envelope from every certified candidate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The unrounded sharp cutoff preserves the small-input branch and intersects
the refined base, thirteen finite constants, both analytic families and eight high profiles.
Every candidate retains its certified guard and uses the base when inactive. -/
noncomputable def sharpWitnessEnvelope (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n
  else
    sharpGuardMin (Real.log n) (lowFiniteWitness n) (Analysis.gaussianLowFamily (Real.log n))
      (Analysis.gaussianSeededSharp (Real.log n)) (sharpHighMin (Real.log n) (lowFiniteWitness n))

/-- The exact interval form of the same guarded sharp cutoff.
It uses the thirteen finite intervals and the selected analytic guard assembly. -/
noncomputable def sharpSelectedEnvelope (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n
  else
    sharpGuardSelected (Real.log n) (lowFiniteSelected n) (Analysis.gaussianLowFamily (Real.log n))
      (Analysis.gaussianSeededSharp (Real.log n)) (sharpHighMin (Real.log n) (lowFiniteSelected n))

/-- The total prime rounding of the unrounded sharp cutoff.
It preserves actual rejecting primes and never enlarges the cutoff. -/
noncomputable def sharpPrimeEnvelope (n : ℕ) : ℝ :=
  primeRound (sharpWitnessEnvelope n)

/-- For every input above one, the guarded and selected sharp functions agree.
This numerical identity requires no parity, compositeness or GRH hypothesis. -/
theorem sharp_eq_selected {n : ℕ} (hn : 1 < n) :
    sharpWitnessEnvelope n = sharpSelectedEnvelope n := by
  simp only [sharpWitnessEnvelope, sharpSelectedEnvelope, lowFinite_eq_selected hn,
    sharpGuardMin_eq_selected]

/-- Every input below 3000 retains the small-interval unrounded cutoff. -/
theorem sharpWitness_eq_small {n : ℕ} (hN : n < 3000) :
    sharpWitnessEnvelope n = smallIntervalBound n :=
  ite_eq_left hN

/-- Every input below 3000 retains the small-interval selected cutoff. -/
theorem sharpSelected_eq_small {n : ℕ} (hN : n < 3000) :
    sharpSelectedEnvelope n = smallIntervalBound n :=
  ite_eq_left hN

/-- The sharp unrounded cutoff never exceeds its thirteen-candidate base.
Resolve the preserved small branch or project its outer minimum. -/
theorem sharpWitness_le_low (n : ℕ) : sharpWitnessEnvelope n ≤ lowFiniteWitness n := by
  by_cases hN : n < 3000
  · rw [sharpWitness_eq_small hN, lowFiniteWitness_eq_small hN]
  · rw [sharpWitnessEnvelope, ite_eq_right hN]
    exact min_le_left _ _

/-- For every input above one, the sharp unrounded cutoff is below the current refined cutoff.
Compose the two numerical minimum projections without analytic assumptions. -/
theorem sharpWitness_le_refined {n : ℕ} (hn : 1 < n) :
    sharpWitnessEnvelope n ≤ refinedWitnessEnvelope n := by
  exact (sharpWitness_le_low n).trans (lowFiniteWitness_le_refined hn)

/-- For inputs above one, the sharp selection never exceeds the current refined selection.
Rewrite the numerical selection identities before applying the unrounded comparison. -/
theorem sharpSelected_le_refined {n : ℕ} (hn : 1 < n) :
    sharpSelectedEnvelope n ≤ refinedSelectedEnvelope n := by
  rw [← sharp_eq_selected hn, ← refined_eq_selected hn]
  exact sharpWitness_le_refined hn

/-- For inputs above one, the rounded sharp cutoff never exceeds the rounded current cutoff.
Use monotonicity of the same total prime-rounding function on both sides. -/
theorem sharpPrime_le_refinedPrime {n : ℕ} (hn : 1 < n) :
    sharpPrimeEnvelope n ≤ refinedPrimeEnvelope n := by
  exact primeRound_mono (sharpWitness_le_refined hn)

/-- For inputs above one, prime rounding never enlarges the sharp selected value. -/
theorem sharpPrime_le_selected {n : ℕ} (hn : 1 < n) :
    sharpPrimeEnvelope n ≤ sharpSelectedEnvelope n := by
  rw [← sharp_eq_selected hn]
  exact primeRound_le _

/-- Above the small-input branch, a common lower bound for the finite base and every
valid Gaussian, seeded and triangular candidate bounds the complete sharp cutoff.
This interface transfers one actual least prime to the guarded minimum. -/
theorem sharp_lower_of_candidates {n : ℕ} (hN : 3000 ≤ n) {C : ℝ} (hB : C ≤ lowFiniteWitness n)
    (hG : 63 ≤ Real.log n → C ≤ Analysis.gaussianLowFamily (Real.log n))
    (hS : 63 ≤ Real.log n → C ≤ Analysis.gaussianSeededSharp (Real.log n))
    (hH :
      ∀ i : Fin 8,
        (Analysis.triangularProfile i).T ≤ Real.log n →
          C ≤ (Analysis.triangularProfile i).C * Real.log n ^ 2) :
    C ≤ sharpWitnessEnvelope n := by
  rw [sharpWitnessEnvelope, ite_eq_right (not_lt.mpr hN)]
  exact sharpGuard_lower hB hG hS (sharpHigh_lower hB hH)

/-- Logarithmic scale at least 63 forces the natural input to be at least 3000.
Use the certified logarithm bound for every smaller natural input, including zero. -/
theorem large_of_log63 {n : ℕ} (hL : 63 ≤ Real.log n) : 3000 ≤ n := by
  by_contra hn
  exact (not_lt.mpr hL) (log_lt63_of_small (lt_of_not_ge hn))

/-- On its certified scale domain, the sharp cutoff is below the fine Gaussian family.
The logarithmic entrance also deactivates the explicit small-input branch. -/
theorem sharp_le_gaussian {n : ℕ} (hL : 63 ≤ Real.log n) :
    sharpWitnessEnvelope n ≤ Analysis.gaussianLowFamily (Real.log n) := by
  rw [sharpWitnessEnvelope, ite_eq_right (not_lt.mpr (large_of_log63 hL))]
  have h :
    sharpGuardMin (Real.log n) (lowFiniteWitness n) (Analysis.gaussianLowFamily (Real.log n))
        (Analysis.gaussianSeededSharp (Real.log n))
        (sharpHighMin (Real.log n) (lowFiniteWitness n)) ≤
      if 63 ≤ Real.log n then Analysis.gaussianLowFamily (Real.log n) else lowFiniteWitness n :=
    (min_le_right _ _).trans (min_le_left _ _)
  simpa only [ite_eq_left hL] using h

/-- On its certified scale domain, the sharp cutoff is below the fine seeded family.
Project its active analytic guard in the unrounded minimum. -/
theorem sharp_le_seeded {n : ℕ} (hL : 63 ≤ Real.log n) :
    sharpWitnessEnvelope n ≤ Analysis.gaussianSeededSharp (Real.log n) := by
  rw [sharpWitnessEnvelope, ite_eq_right (not_lt.mpr (large_of_log63 hL))]
  have h :
    sharpGuardMin (Real.log n) (lowFiniteWitness n) (Analysis.gaussianLowFamily (Real.log n))
        (Analysis.gaussianSeededSharp (Real.log n))
        (sharpHighMin (Real.log n) (lowFiniteWitness n)) ≤
      if 63 ≤ Real.log n then Analysis.gaussianSeededSharp (Real.log n) else lowFiniteWitness n :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  simpa only [ite_eq_left hL] using h

/-- Above a triangular profile entrance, the sharp cutoff is below that profile.
Project the active high minimum after excluding the small-input branch. -/
theorem sharp_le_triangular {n : ℕ} (i : Fin 8)
    (hL : (Analysis.triangularProfile i).T ≤ Real.log n) :
    sharpWitnessEnvelope n ≤ (Analysis.triangularProfile i).C * Real.log n ^ 2 := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [(Analysis.triangularProfile i).entry, hL]
  rw [sharpWitnessEnvelope, ite_eq_right (not_lt.mpr (large_of_log63 h63))]
  exact
    (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (sharpHigh_le_profile _ _ i hL)))

/-- Under GRH, each odd composite above one has a least rejecting prime below the sharp cutoff.
Start with an actual current least prime and transfer every new actual witness through leastness.
The small branch uses its existing actual refined witness bound. -/
theorem exists_least_sharpEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ sharpWitnessEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_refinedEnvelope hn ho hc hGRH
  have transfer {C : ℝ}
    (hw : ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ C ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n)) :
    (p : ℝ) ≤ C := by
    obtain ⟨q, hq, hqb, hqr⟩ := hw
    exact (Nat.cast_le.mpr (hm q hq hqr)).trans hqb
  by_cases hN : n < 3000
  · refine ⟨p, hp, hr, ?_, hm⟩
    rw [sharpWitness_eq_small hN, ← refined_eq_small hn hN]
    exact hb
  · have hB : (p : ℝ) ≤ lowFiniteWitness n :=
      lowFinite_lower_of_candidates hn hb
        (fun f hL ↦ transfer (exists_prime_finitePrincipal f hn ho hc hGRH hL))
    refine ⟨p, hp, hr, sharp_lower_of_candidates (le_of_not_gt hN) hB ?_ ?_ ?_, hm⟩
    · intro hL; exact transfer (exists_prime_gaussianLowFamily ho hc hGRH hL)
    · intro hL; exact transfer (exists_prime_seededSharpSelected ho hc hGRH hL)
    · intro i hL; exact transfer (exists_prime_triangularProfile _ hn ho hc hGRH hL)

/-- Under GRH, the sharp unrounded cutoff contains an actual rejecting prime.
Forget minimality from the common least-prime theorem. -/
theorem exists_prime_sharpEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ sharpWitnessEnvelope n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_sharpEnvelope hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩

/-- Under GRH, the selected sharp cutoff contains the least rejecting prime.
Transfer the actual unrounded witness through the numerical selection identity. -/
theorem exists_least_sharpSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ sharpSelectedEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  rw [← sharp_eq_selected hn]
  exact exists_least_sharpEnvelope hn ho hc hGRH

/-- Under GRH, the selected sharp cutoff contains an actual rejecting prime.
The numerical identity preserves both primality and Miller-Rabin rejection. -/
theorem exists_prime_sharpSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ sharpSelectedEnvelope n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rw [← sharp_eq_selected hn]
  exact exists_prime_sharpEnvelope hn ho hc hGRH

/-- Under GRH, rounding preserves the same actual least rejecting prime.
Apply prime-preserving rounding to its unrounded numerical bound. -/
theorem exists_least_sharpPrimeEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ sharpPrimeEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_sharpEnvelope hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

/-- Under GRH, the rounded sharp cutoff contains an actual rejecting prime.
Extract it from the rounded least-prime theorem. -/
theorem exists_prime_sharpPrimeEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ sharpPrimeEnvelope n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_sharpPrimeEnvelope hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
