/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundCountTheta
public import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeEleventhsPhaseInputs
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundTheta

/-! # Remaining theta and zero-count inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the Euler-normalized Riemann–von Mangoldt identity and the
displayed Gamma-phase error bound imply the `3/11` least-witness theorem for
every odd composite. The Backlund phase estimate and the coarse zero count
are proved internally. -/
theorem three_eleven_least_of_theta {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hV : AnalyticNumberTheory.RiemannZeta.EulerRiemannVonMangoldt)
    (hG :
      ∀ t : ℝ,
        2 * Real.pi * Real.exp 1 ≤ t →
          |AnalyticNumberTheory.RiemannZeta.backlundTheta t -
                AnalyticNumberTheory.RiemannZeta.backlundThetaMain t| ≤
            1 / (4 * t)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  apply
    three_eleven_least_of_euler_phase hn ho hc hGRH
      (AnalyticNumberTheory.RiemannZeta.euler_phase_count_of_riemann_von_mangoldt hV)
  intro t ht
  have hbase : 0 < 2 * Real.pi * Real.exp 1 :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)
  exact AnalyticNumberTheory.RiemannZeta.theta_error_le_of_phase (hbase.trans_le ht) (hG t ht)

end PseudoPrime.PrimeTestBounds.MillerRabin
