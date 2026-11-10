/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterVariableAnchor

/-! # Quarter-square uniform triple anchor 10 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- This rational anchor gives a quarter-square rejecting prime for a uniform
Korselt triple on its stated logarithmic interval. The correction is checked
by rational arithmetic and primality rounds the radius bound. -/
theorem quarter_uniform_anchor10 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (20 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 108 / 5) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hc :=
    localCorrectionCheck_sound
      (show localCorrectionCheck (10) (36001 / 10000) 4 = true by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hd : (18 / 5 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (10 : ℝ) := by
    linarith only [hc]
  have hP : (97 : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  have hround : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (10 : ℝ) ^ 2 → (p : ℝ) ≤ 97 := by
    intro p hp hpbound
    have hlt : p < 101 := by
      have h : (p : ℝ) < 101 := by nlinarith only [hpbound]
      exact_mod_cast h
    have hpmax : p ≤ 100 := Nat.lt_succ_iff.mp hlt
    have hpP : p ≤ 97 := by
      by_contra h
      have hnp : ∀ k ∈ Finset.Icc 98 100, ¬Nat.Prime k := by decide +kernel
      exact hnp p (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.lt_of_not_ge h), hpmax⟩) hp
    exact_mod_cast hpP
  exact
    quarter_uniform_variable hn ho hu hGRH (by linarith only [hL]) (b := 10) (d := 18 / 5) (P := 97)
      (by norm_num only) hd (by norm_num only) (by linarith only [hU]) hP hround

end PseudoPrime.PrimeTestBounds.MillerRabin
