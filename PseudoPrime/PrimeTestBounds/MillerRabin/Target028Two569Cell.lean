/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028TwoGroups
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Two569Grid
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EvenEnvelope

/-! # First two-group semiprime interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Two weighted prime groups yield a 0.28 witness for distinct semiprimes
at logarithmic scales from 96.708 to 99.677 under GRH. -/
theorem target028_semiprime_96708_99677 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (96708 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 99677 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_two2618 hn ho hp hq hpq hprod hGRH 569 738183894796975557
      target028Two569_count (D := (41142 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 738183894796975557 60 32 (41142 / 1000) 43 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (96708 / 1000 : ℝ)) (hi := (99677 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

end PseudoPrime.PrimeTestBounds.MillerRabin
