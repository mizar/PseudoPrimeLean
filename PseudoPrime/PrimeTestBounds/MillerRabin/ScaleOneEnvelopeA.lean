/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ScaleOneIndex
public import PseudoPrime.PrimeTestBounds.MillerRabin.SmoothDualEnvelope

/-! # Stage A scale-one pointwise upper envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Intersect the existing envelope with the scale-one Gaussian candidate from 25000. -/
noncomputable def scaleOneSelectedA (n : ℕ) : ℝ :=
  if (25000 : ℝ) ≤ Real.log n then
    min (smoothSelected n) (((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2) * Real.log n ^ 2)
  else smoothSelected n

/-- Round the stage A selection to the largest admissible prime. -/
noncomputable def scaleOnePrimeA (n : ℕ) : ℝ :=
  primeRound (scaleOneSelectedA n)

/-- The new selection is no larger than the existing envelope. -/
theorem scaleOneSelectedA_le (n : ℕ) : scaleOneSelectedA n ≤ smoothSelected n := by
  unfold scaleOneSelectedA
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- Under GRH, the least rejecting prime lies below the stage A selection. -/
theorem exists_least_scaleOneSelectedA {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ scaleOneSelectedA n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_smoothSelected hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  by_cases hL : (25000 : ℝ) ≤ Real.log n
  · rw [scaleOneSelectedA, ite_eq_left hL]
    obtain ⟨q, hq, hqb, hqr⟩ := prime_witness_scaleOne hn ho hc hGRH hL
    exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
  · rw [scaleOneSelectedA, ite_eq_right hL]
    exact hb

/-- Under GRH, prime rounding preserves the least rejecting prime. -/
theorem exists_least_scaleOnePrimeA {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ scaleOnePrimeA n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_scaleOneSelectedA hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

/-- Both stage A selections preserve the value three on the certified small interval. -/
theorem scaleOne_smallA {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    scaleOneSelectedA n = 3 ∧ scaleOnePrimeA n = 3 := by
  have hlog : Real.log n < 25000 := lt_trans (log_lt63_of_small hu) (by norm_num only)
  have he : scaleOneSelectedA n = smoothSelected n := ite_eq_right (not_le_of_gt hlog)
  have hh := smooth_small_three hl hu
  constructor
  · exact he.trans hh.1
  · change primeRound (scaleOneSelectedA n) = 3
    rw [he]
    exact hh.2

/-- The stage A selection is monotone on the interval where it is constantly three. -/
theorem scaleOne_small_monoA : MonotoneOn scaleOneSelectedA (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [(scaleOne_smallA hm.1 hm.2).1, (scaleOne_smallA hn.1 hn.2).1]

end PseudoPrime.PrimeTestBounds.MillerRabin
