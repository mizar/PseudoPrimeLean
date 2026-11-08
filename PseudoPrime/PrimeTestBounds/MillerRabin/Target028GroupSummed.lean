/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Group506
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GroupWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EvenEnvelope

/-! # Semiprime interval from a summed grouped count -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Summing the numbers of added prime factors gives a 0.28 witness for
distinct semiprimes with logarithmic scale between 85.926 and 88.181. -/
theorem target028_semiprime_85926_88181 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (85926 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 88181 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_group hn ho hp hq hpq hprod hGRH 506 5765473899816181
      target028_group506_count (D := (36290 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 5765473899816181 53 32 (36290 / 1000) 38 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (85926 / 1000 : ℝ)) (hi := (88181 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

end PseudoPrime.PrimeTestBounds.MillerRabin
