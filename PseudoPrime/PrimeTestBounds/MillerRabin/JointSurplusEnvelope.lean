/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusGlobal
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCumulative
public import PseudoPrime.PrimeTestBounds.MillerRabin.JointSurplusDominance

/-! # Global surplus minimum and public pointwise envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the least rejecting prime is below all three global candidates. -/
theorem jointSurplus_least_bound {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (compositeLeastPrime n : ℝ) ≤ jointSurplusGlobal (Real.log n) := by
  have hs := compositeLeastPrime_spec hGRH hn ho hc
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_four_ninths hn ho hc hGRH
  obtain ⟨q, hq, hqb, hqf⟩ := jointSurplus_global35000 hn ho hc hGRH
  obtain ⟨r, hr, hrb, hrf⟩ := jointSurplus_global50000 hn ho hc hGRH
  unfold jointSurplusGlobal
  refine le_min ?_ (le_min ?_ ?_)
  · exact (Nat.cast_le.mpr (hs.2.2 p hp hf)).trans hb
  · exact (Nat.cast_le.mpr (hs.2.2 q hq hqf)).trans hqb
  · exact (Nat.cast_le.mpr (hs.2.2 r hr hrf)).trans hrb

/-- The global comparison function bounds an actual least rejecting prime under GRH. -/
theorem jointSurplus_least {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ jointSurplusGlobal (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let p := compositeLeastPrime n
  have hs := compositeLeastPrime_spec hGRH hn ho hc
  exact ⟨p, hs.1, hs.2.1, jointSurplus_least_bound hn ho hc hGRH, hs.2.2⟩

/-- Preserve the existing small-input selection and intersect the global candidate
with the previous public envelope for inputs at least 3000. -/
noncomputable def jointSelected (n : ℕ) : ℝ :=
  if n < 3000 then scaleOneSelectedA n else min (smoothSelected n) (jointSurplusGlobal (Real.log n))

/-- Prime rounding of the global joint selection. -/
noncomputable def jointPrime (n : ℕ) : ℝ :=
  primeRound (jointSelected n)

/-- The joint selection does not exceed the preceding public envelope. -/
theorem jointSelected_le (n : ℕ) : jointSelected n ≤ scaleOneSelectedA n := by
  unfold jointSelected
  by_cases hn : n < 3000
  · rw [ite_eq_left hn]
  · rw [ite_eq_right hn, scaleOneSelectedA]
    by_cases h : (25000 : ℝ) ≤ Real.log n
    · rw [ite_eq_left h]
      apply le_min (min_le_left _ _)
      have hc : jointSurplusGlobal (Real.log n) ≤ jointSurplusCutoff 155 29 (Real.log n) :=
        (min_le_right _ _).trans (min_le_right _ _)
      exact (min_le_right _ _).trans (hc.trans (jointSurplus_lt_adaptive h).le)
    · rw [ite_eq_right h]
      exact min_le_left _ _

/-- Under GRH, the joint selection bounds a least rejecting prime. -/
theorem jointSelected_least {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ jointSelected n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_scaleOneSelectedA hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  by_cases hn3 : n < 3000
  · rw [jointSelected, ite_eq_left hn3]
    exact hb
  · rw [jointSelected, ite_eq_right hn3]
    obtain ⟨q, hq, hqr, hqb, _⟩ := jointSurplus_least hn ho hc hGRH
    exact le_min (hb.trans (scaleOneSelectedA_le n)) ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)

/-- Under GRH, prime rounding preserves the least rejecting prime. -/
theorem jointPrime_least {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ jointPrime n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := jointSelected_least hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

/-- Both selections retain the certified value three on the small interval. -/
theorem joint_small {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    jointSelected n = 3 ∧ jointPrime n = 3 := by
  have he : jointSelected n = scaleOneSelectedA n := ite_eq_left hu
  have hh := scaleOne_smallA hl hu
  constructor
  · exact he.trans hh.1
  · change primeRound (jointSelected n) = 3
    rw [he]
    exact hh.2

/-- The joint selection is monotone on the interval where it is constantly three. -/
theorem joint_small_mono : MonotoneOn jointSelected (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [(joint_small hm.1 hm.2).1, (joint_small hn.1 hn.2).1]

end PseudoPrime.PrimeTestBounds.MillerRabin
