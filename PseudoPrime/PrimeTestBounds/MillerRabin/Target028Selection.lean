/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cumulative
public import PseudoPrime.PrimeTestBounds.MillerRabin.JointSurplusCumulative

/-! # Pointwise and cumulative selections with the 0.28 bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Intersect the existing pointwise selection with the global 0.28
maximum bound. This retains every previous pointwise improvement. -/
noncomputable def target028Selected (n : ℕ) : ℝ :=
  min (jointSelected n) (max 2 ((7 / 25 : ℝ) * Real.log n ^ 2))

/-- Intersect the existing cumulative envelope with the global 0.28
maximum bound. This retains the previous cumulative history. -/
noncomputable def target028Cumulative (N : ℕ) : ℝ :=
  min (jointCumulative N) (max 2 ((7 / 25 : ℝ) * Real.log N ^ 2))

/-- Under GRH, the new selection bounds the least rejecting prime for every odd
composite above one. Combine the old selection and the global actual witness. -/
theorem target028Selected_least {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ target028Selected n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := jointSelected_least hn ho hc hGRH
  obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_reject_028_global hGRH hn ho hc
  refine ⟨p, hp, hr, ?_, hm⟩
  change (p : ℝ) ≤ min (jointSelected n) (max 2 ((7 / 25 : ℝ) * Real.log n ^ 2))
  exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)

/-- Under GRH, the new cumulative selection bounds the cumulative least prime
at every natural endpoint. Combine the two certified cumulative bounds. -/
theorem cumulativeLeastPrime_le_target028
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ target028Cumulative N := by
  exact le_min (cumulativeLeastPrime_le_joint hGRH N) (cumulativeLeastPrime_le_028 hGRH N)

/-- Round the new pointwise cutoff down to the greatest prime it admits.
The selected least rejecting prime remains within this rounded cutoff. -/
noncomputable def target028Prime (n : ℕ) : ℝ :=
  primeRound (target028Selected n)

/-- Under GRH, prime rounding preserves the least rejecting prime and its
minimality for each odd composite above one. -/
theorem target028Prime_least {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ target028Prime n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := target028Selected_least hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

/-- The selected and rounded cutoffs both remain three on the entire interval
from 2047 to 2999. The certified logarithm bound makes the new max cutoff
at least three, so the previous small-input value is preserved. -/
theorem target028_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    target028Selected n = 3 ∧ target028Prime n = 3 := by
  have hlog2047 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2047 11 12 7 8 = true by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hlog2047
  have ht := Real.log_le_log (by norm_num only : (0 : ℝ) < 2047) (Nat.cast_le.mpr hl)
  have h7 : (7 : ℝ) ≤ Real.log n := hlog2047.trans ht
  have hs7 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 7) h7 2
  have hb : (3 : ℝ) ≤ max 2 ((7 / 25 : ℝ) * Real.log n ^ 2) :=
    (show (3 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 by nlinarith only [hs7]).trans (le_max_right _ _)
  have he : target028Selected n = 3 := by
    rw [target028Selected, (joint_small hl hu).1, min_eq_left hb]
  constructor
  · exact he
  · change primeRound (target028Selected n) = 3
    rw [he]
    simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

end PseudoPrime.PrimeTestBounds.MillerRabin
