/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028TwoSupply2781
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Two585Grid
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EvenEnvelope

/-! # Two-group semiprime interval through scale 102.062 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The two-group count yields a 0.28 semiprime witness on
`[99677/1000, 102062/1000]` under GRH. -/
theorem target028_two_final_cell0 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (99677 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 102062 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_two2781 hn ho hp hq hpq hprod hGRH 585 2267282102077273571
      target028Two585_count (D := (42265 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 2267282102077273571 61 32 (42265 / 1000) 44 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (99677 / 1000 : ℝ)) (hi := (102062 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

end PseudoPrime.PrimeTestBounds.MillerRabin
