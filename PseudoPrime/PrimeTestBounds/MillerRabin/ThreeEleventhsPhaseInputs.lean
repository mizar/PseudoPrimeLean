/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundCountPhase
public import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeEleventhsZeroCount
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundEulerLog
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundPhaseNumerics
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CoarseZeroCountNumerics

/-! # Three-elevenths bound from normalized phase inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the Euler-normalized good-height counting identity and the
stated Gamma-phase error bound imply the least-prime `3/11` witness bound for
every odd composite. The Backlund argument and coarse count are discharged
internally; the counting identity and Gamma error remain explicit inputs. -/
theorem three_eleven_least_of_euler_phase {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {E : ℝ → ℝ}
    (hid : AnalyticNumberTheory.RiemannZeta.EulerPhaseCountIdentity E)
    (hE : ∀ t : ℝ, 2 * Real.pi * Real.exp 1 ≤ t → |E t| ≤ 1 / (5 * t)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact
    three_eleven_least_of_coarse_count hn ho hc hGRH
      (AnalyticNumberTheory.RiemannZeta.coarse_count_of_euler_phase hid hE)

end PseudoPrime.PrimeTestBounds.MillerRabin
