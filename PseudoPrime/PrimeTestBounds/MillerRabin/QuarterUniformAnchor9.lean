/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterVariableAnchor

/-! # Quarter-square uniform triple anchor 9 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- This rational anchor gives a quarter-square rejecting prime for a uniform
Korselt triple on its stated logarithmic interval. The correction is checked
by rational arithmetic and primality rounds the radius bound. -/
theorem quarter_uniform_anchor9 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (18 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 1029 / 50) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hc :=
    localCorrectionCheck_sound
      (show localCorrectionCheck (9) (34301 / 10000) 4 = true by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hd : (343 / 100 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (9 : ℝ) := by
    linarith only [hc]
  have hP : (79 : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  have hround : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (9 : ℝ) ^ 2 → (p : ℝ) ≤ 79 := by
    intro p hp hpbound
    have hlt : p < 82 := by
      have h : (p : ℝ) < 82 := by nlinarith only [hpbound]
      exact_mod_cast h
    have hpmax : p ≤ 81 := Nat.lt_succ_iff.mp hlt
    have hpP : p ≤ 79 := by
      by_contra h
      have hnp : ∀ k ∈ Finset.Icc 80 81, ¬Nat.Prime k := by decide +kernel
      exact hnp p (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.lt_of_not_ge h), hpmax⟩) hp
    exact_mod_cast hpP
  exact
    quarter_uniform_variable hn ho hu hGRH (by linarith only [hL]) (b := 9) (d := 343 / 100) (P :=
      79) (by norm_num only) hd (by norm_num only) (by linarith only [hU]) hP hround

end PseudoPrime.PrimeTestBounds.MillerRabin
