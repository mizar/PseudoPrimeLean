/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAdaptiveComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedFixedProfiles

/-! # Fixed profile candidates combined with the adaptive envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Add a certified fixed profile to the Gaussian-selected cutoff when its entrance holds. -/
noncomputable def fixedProfileSelected (f : TriangularProfile) (n : ℕ) : ℝ :=
  if f.T ≤ Real.log n then min (gaussianAdaptiveSelected n) (f.C * Real.log n ^ 2)
  else gaussianAdaptiveSelected n

/-- The fixed-profile selection retains the Gaussian cutoff and all three certified candidates. -/
noncomputable def fixedImprovedSelected (n : ℕ) : ℝ :=
  min (fixedProfileSelected improvedProfile03869 n)
    (min (fixedProfileSelected improvedProfile03552 n)
      (fixedProfileSelected improvedProfile03134 n))

/-- Under GRH, leastness transfers a profile's actual witness bound to the selected cutoff. -/
theorem fixedProfile_least_bound (f : TriangularProfile) {n p : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hb : (p : ℝ) ≤ gaussianAdaptiveSelected n)
    (hm : ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q) :
    (p : ℝ) ≤ fixedProfileSelected f n := by
  by_cases hL : f.T ≤ Real.log n
  · rw [fixedProfileSelected, ite_eq_left hL]
    obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_triangularProfile f hn ho hc hGRH hL
    exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
  · rw [fixedProfileSelected, ite_eq_right hL]
    exact hb

/-- Under GRH, the least rejecting prime of an odd composite lies below the
fixed-profile selection. -/
theorem exists_least_fixedImproved {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ fixedImprovedSelected n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_gaussianAdaptive hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  exact
    le_min (fixedProfile_least_bound improvedProfile03869 hn ho hc hGRH hb hm)
      (le_min (fixedProfile_least_bound improvedProfile03552 hn ho hc hGRH hb hm)
        (fixedProfile_least_bound improvedProfile03134 hn ho hc hGRH hb hm))

/-- Prime rounding of the fixed-profile selection retains every prime below the cutoff. -/
noncomputable def fixedImprovedPrime (n : ℕ) : ℝ :=
  primeRound (fixedImprovedSelected n)

/-- Under GRH, rounding preserves the least rejecting prime below the fixed-profile selection. -/
theorem exists_least_fixedImprovedPrime {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ fixedImprovedPrime n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_fixedImproved hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
