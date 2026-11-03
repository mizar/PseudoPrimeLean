/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighWindowBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighCoefficientEnvelope

/-! # Pointwise selected and prime-rounded high-window witness bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The selected real cutoff keeps the previous value below 3000 and intersects it with
the strongest applicable high-window candidate at logarithmic entrances 38, 45, 60 and 80 billion.
The old cutoff remains available at every input. -/
noncomputable def highWindowSelected (n : ℕ) : ℝ :=
  if n < 3000 then highCoeffSelected n
  else
    if (80000000000 : ℝ) ≤ Real.log n then
      min (highCoeffSelected n) ((173 / 500 : ℝ) * Real.log n ^ 2)
    else
      if (60000000000 : ℝ) ≤ Real.log n then
        min (highCoeffSelected n) ((369 / 1000 : ℝ) * Real.log n ^ 2)
      else
        if (45000000000 : ℝ) ≤ Real.log n then
          min (highCoeffSelected n) ((2 / 5 : ℝ) * Real.log n ^ 2)
        else
          if (38000000000 : ℝ) ≤ Real.log n then
            min (highCoeffSelected n) ((423 / 1000 : ℝ) * Real.log n ^ 2)
          else highCoeffSelected n

/-- The prime-rounded high-window cutoff preserves all prime witnesses below the selected
real cutoff. It supplies the public prime-valued variant of the new envelope. -/
noncomputable def highWindowPrime (n : ℕ) : ℝ :=
  primeRound (highWindowSelected n)

/-- The high-window selection never exceeds the previous selected cutoff. -/
theorem highWindowSelected_le_previous (n : ℕ) : highWindowSelected n ≤ highCoeffSelected n := by
  by_cases hN : n < 3000
  · rw [highWindowSelected, ite_eq_left hN]
  · rw [highWindowSelected, ite_eq_right hN]
    by_cases h80 : (80000000000 : ℝ) ≤ Real.log n
    · rw [ite_eq_left h80]
      exact min_le_left _ _
    · rw [ite_eq_right h80]
      by_cases h60 : (60000000000 : ℝ) ≤ Real.log n
      · rw [ite_eq_left h60]
        exact min_le_left _ _
      · rw [ite_eq_right h60]
        by_cases h45 : (45000000000 : ℝ) ≤ Real.log n
        · rw [ite_eq_left h45]
          exact min_le_left _ _
        · rw [ite_eq_right h45]
          by_cases h38 : (38000000000 : ℝ) ≤ Real.log n
          · rw [ite_eq_left h38]
            exact min_le_left _ _
          · rw [ite_eq_right h38]

/-- Prime rounding preserves the non-worsening comparison with the previous prime cutoff. -/
theorem highWindowPrime_le_previous (n : ℕ) : highWindowPrime n ≤ highCoeffPrime n :=
  primeRound_mono (highWindowSelected_le_previous n)

/-- In the first high window, the selected cutoff is at most 423/1000 of the squared logarithm. -/
theorem highWindowSelected_le_0423 {n : ℕ} (hN : 3000 ≤ n) (hL : (38000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 45000000000) : highWindowSelected n ≤ (423 / 1000 : ℝ) * Real.log n ^ 2 := by
  have h60 : ¬(60000000000 : ℝ) ≤ Real.log n := not_le_of_gt (lt_of_lt_of_le hU (by norm_num only))
  have h80 : ¬(80000000000 : ℝ) ≤ Real.log n := not_le_of_gt (lt_of_lt_of_le hU (by norm_num only))
  rw [highWindowSelected, ite_eq_right (not_lt.mpr hN), ite_eq_right h80, ite_eq_right h60,
    ite_eq_right (not_le_of_gt hU), ite_eq_left hL]
  exact min_le_right _ _

/-- In the next high window, the selected cutoff is at most two fifths of the squared logarithm. -/
theorem highWindowSelected_le_040 {n : ℕ} (hN : 3000 ≤ n) (hL : (45000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 60000000000) : highWindowSelected n ≤ (2 / 5 : ℝ) * Real.log n ^ 2 := by
  have h80 : ¬(80000000000 : ℝ) ≤ Real.log n := not_le_of_gt (lt_of_lt_of_le hU (by norm_num only))
  rw [highWindowSelected, ite_eq_right (not_lt.mpr hN), ite_eq_right h80,
    ite_eq_right (not_le_of_gt hU), ite_eq_left hL]
  exact min_le_right _ _

/-- In the second high window, the selected cutoff is at most 369/1000 of the squared logarithm. -/
theorem highWindowSelected_le_0369 {n : ℕ} (hN : 3000 ≤ n) (hL : (60000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 80000000000) : highWindowSelected n ≤ (369 / 1000 : ℝ) * Real.log n ^ 2 := by
  rw [highWindowSelected, ite_eq_right (not_lt.mpr hN), ite_eq_right (not_le_of_gt hU),
    ite_eq_left hL]
  exact min_le_right _ _

/-- Above the third entrance, the selected cutoff is at most 173/500 of the squared logarithm. -/
theorem highWindowSelected_le_0346 {n : ℕ} (hN : 3000 ≤ n) (hL : (80000000000 : ℝ) ≤ Real.log n) :
    highWindowSelected n ≤ (173 / 500 : ℝ) * Real.log n ^ 2 := by
  rw [highWindowSelected, ite_eq_right (not_lt.mpr hN), ite_eq_left hL]
  exact min_le_right _ _

/-- Below 3000 the high-window selection agrees with the previous selection. -/
theorem highWindowSelected_small {n : ℕ} (h : n < 3000) :
    highWindowSelected n = highCoeffSelected n := by exact ite_eq_left h

/-- On the exact interval from 2047 inclusive to 3000 exclusive, the selected cutoff is three. -/
theorem highWindowSelected_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    highWindowSelected n = 3 := by
  exact (highWindowSelected_small hu).trans (highCoeffSelected_small_three hl hu)

/-- Prime rounding preserves the cutoff three on the same small interval. -/
theorem highWindowPrime_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    highWindowPrime n = 3 := by
  rw [highWindowPrime, highWindowSelected_small hu]
  exact highCoeffPrime_small_three hl hu

/-- The new selection is nondecreasing on the preserved constant-three interval. -/
theorem highWindowSelected_small_mono : MonotoneOn highWindowSelected (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [highWindowSelected_small_three hm.1 hm.2, highWindowSelected_small_three hn.1 hn.2]

/-- The rounded cutoff is nondecreasing on the preserved constant-three interval. -/
theorem highWindowPrime_small_mono : MonotoneOn highWindowPrime (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [highWindowPrime_small_three hm.1 hm.2, highWindowPrime_small_three hn.1 hn.2]

/-- Under GRH, every odd composite above one has its least rejecting prime below the new
selected cutoff. The previous least witness is bounded by each active profile via leastness. -/
theorem exists_least_highWindowSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ highWindowSelected n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_highCoeffSelected hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  by_cases hN : n < 3000
  · rw [highWindowSelected, ite_eq_left hN]
    exact hb
  · rw [highWindowSelected, ite_eq_right hN]
    by_cases h80 : (80000000000 : ℝ) ≤ Real.log n
    · rw [ite_eq_left h80]
      obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_highWindowP0346 hn ho hc hGRH h80
      exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
    · rw [ite_eq_right h80]
      by_cases h60 : (60000000000 : ℝ) ≤ Real.log n
      · rw [ite_eq_left h60]
        obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_highWindowP0369 hn ho hc hGRH h60
        exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
      · rw [ite_eq_right h60]
        by_cases h45 : (45000000000 : ℝ) ≤ Real.log n
        · rw [ite_eq_left h45]
          obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_highWindowP040 hn ho hc hGRH h45
          exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
        · rw [ite_eq_right h45]
          by_cases h38 : (38000000000 : ℝ) ≤ Real.log n
          · rw [ite_eq_left h38]
            obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_highWindowP0423 hn ho hc hGRH h38
            exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
          · rw [ite_eq_right h38]
            exact hb

/-- Under GRH, prime rounding retains the least rejecting prime below the selected cutoff.
The result needs no global monotonicity of the pointwise envelope. -/
theorem exists_least_highWindowPrime {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ highWindowPrime n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_highWindowSelected hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
