/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighCoefficientBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsEnvelope

/-! # Selected and prime-rounded high-coefficient witness envelopes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Retain the four-ninths selected envelope below 3000 and before
`log n = 70000`; at later inputs intersect it with `(7 / 16) * log n ^ 2`. -/
noncomputable def highCoeffSelected (n : ℕ) : ℝ :=
  if n < 3000 then fourNinthsSelectedEnvelope n
  else
    if 70000 ≤ Real.log n then min (fourNinthsSelectedEnvelope n) ((7 / 16 : ℝ) * (Real.log n) ^ 2)
    else fourNinthsSelectedEnvelope n

/-- Round the high-coefficient selected cutoff down to a prime, retaining
every prime witness bounded by that cutoff. -/
noncomputable def highCoeffPrime (n : ℕ) : ℝ :=
  primeRound (highCoeffSelected n)

/-- The high-coefficient selected cutoff never exceeds the previous cutoff. -/
theorem highCoeffSelected_le_previous (n : ℕ) :
    highCoeffSelected n ≤ fourNinthsSelectedEnvelope n := by
  by_cases hN : n < 3000
  · rw [highCoeffSelected, ite_eq_left hN]
  · rw [highCoeffSelected, ite_eq_right hN]
    by_cases hL : (70000 : ℝ) ≤ Real.log n
    · rw [ite_eq_left hL]
      exact min_le_left _ _
    · rw [ite_eq_right hL]

/-- At the high entrance and above the small branch, the selected cutoff is
at most seven sixteenths of the squared logarithm. -/
theorem highCoeffSelected_le_quad {n : ℕ} (hN : 3000 ≤ n) (hL : (70000 : ℝ) ≤ Real.log n) :
    highCoeffSelected n ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 := by
  rw [highCoeffSelected, ite_eq_right (not_lt.mpr hN), ite_eq_left hL]
  exact min_le_right _ _

/-- Below 3000 the selected envelope retains the previous selected cutoff. -/
theorem highCoeffSelected_small {n : ℕ} (h : n < 3000) :
    highCoeffSelected n = fourNinthsSelectedEnvelope n :=
  ite_eq_left h

/-- On `2047 ≤ n < 3000`, the selected cutoff remains exactly three. -/
theorem highCoeffSelected_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    highCoeffSelected n = 3 := by
  rw [highCoeffSelected_small hu, fourNinthsSelected_small_three hl hu]

/-- Prime rounding preserves the cutoff three on the same small interval. -/
theorem highCoeffPrime_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    highCoeffPrime n = 3 := by
  rw [highCoeffPrime, highCoeffSelected_small_three hl hu]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

/-- The selected cutoff is monotone on the preserved small interval. -/
theorem highCoeffSelected_small_mono : MonotoneOn highCoeffSelected (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [highCoeffSelected_small_three hm.1 hm.2, highCoeffSelected_small_three hn.1 hn.2]

/-- The prime-rounded cutoff is monotone on the preserved small interval. -/
theorem highCoeffPrime_small_mono : MonotoneOn highCoeffPrime (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [highCoeffPrime_small_three hm.1 hm.2, highCoeffPrime_small_three hn.1 hn.2]

/-- Under GRH, every odd composite above one has its least rejecting prime
below the selected envelope. Above the new entrance, leastness transfers the
separate high-range witness into the minimum. -/
theorem exists_least_highCoeffSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ highCoeffSelected n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_fourNinthsSelected hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  by_cases hN : n < 3000
  · rw [highCoeffSelected, ite_eq_left hN]
    exact hb
  · rw [highCoeffSelected, ite_eq_right hN]
    by_cases hL : (70000 : ℝ) ≤ Real.log n
    · rw [ite_eq_left hL]
      apply le_min hb
      obtain ⟨q, hq, hqb, hqr⟩ := highCoeff_prime_witness hn ho hc hGRH hL
      exact (Nat.cast_le.mpr (hm q hq hqr)).trans hqb
    · rw [ite_eq_right hL]
      exact hb

/-- Under GRH, prime rounding retains the least rejecting prime below the
new cutoff; no monotonicity of the full pointwise envelope is required. -/
theorem exists_least_highCoeffPrime {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ highCoeffPrime n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_highCoeffSelected hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
