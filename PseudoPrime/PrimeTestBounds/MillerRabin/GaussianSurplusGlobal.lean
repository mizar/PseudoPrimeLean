/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusIndex
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusShape
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsBounds

/-! # Global witness bounds from both surplus Gaussian prefixes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the 35000-prefix cutoff bounds an actual rejecting prime for every
odd composite. Below its direct entrance, the four-ninths bound fits under its floor. -/
theorem jointSurplus_global35000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ jointSurplusCutoff 130 30 (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hL : (280 : ℝ) ≤ Real.log n
  · exact jointSurplus_witness35000 hn ho hc hGRH hL
  · obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_four_ninths hn ho hc hGRH
    have hlog0 := Real.log_natCast_nonneg n
    have hsq := (sq_le_sq₀ hlog0 (by norm_num only : (0 : ℝ) ≤ 280)).mpr (le_of_not_ge hL)
    have hr : (130 : ℝ) ≤ jointSurplusRadius 130 30 (Real.log n) := le_max_left _ _
    have hrsq := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 130) hr 2
    have hbound : (4 / 9 : ℝ) * Real.log n ^ 2 ≤ jointSurplusCutoff 130 30 (Real.log n) := by
      unfold jointSurplusCutoff
      nlinarith only [hsq, hrsq]
    exact ⟨p, hp, hb.trans hbound, hf⟩

/-- At the bridging scale, the 35000-prefix cutoff lies below the 50000 floor. -/
theorem jointSurplus_bridge340 : jointSurplusCutoff 130 30 340 < (21 / 10 : ℝ) * (155 : ℝ) ^ 2 := by
  have hroot : jointSurplusRoot 30 340 ≤ (1237 / 100 : ℝ) :=
    Analysis.gaussianBudgetRoot_le_of_budget (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only)
  have hroot0 : 0 ≤ jointSurplusRoot 30 340 :=
    (Analysis.gaussianBudgetRoot_pos (by norm_num only) (by norm_num only)).le
  have hsq := pow_le_pow_left₀ hroot0 hroot 2
  have hr : jointSurplusRadius 130 30 340 ≤ (154 : ℝ) := by
    apply max_le
    · norm_num only
    · nlinarith only [hsq]
  have hr0 : 0 ≤ jointSurplusRadius 130 30 340 :=
    (by norm_num only : (0 : ℝ) ≤ 130).trans (le_max_left _ _)
  have hrsq := pow_le_pow_left₀ hr0 hr 2
  unfold jointSurplusCutoff
  nlinarith only [hrsq]

/-- Under GRH, the 50000-prefix cutoff also bounds an actual rejecting prime for
every odd composite. Below its direct entrance, transfer the 35000 witness through
the certified bridge and monotonicity. -/
theorem jointSurplus_global50000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ jointSurplusCutoff 155 29 (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hL : (340 : ℝ) ≤ Real.log n
  · exact jointSurplus_witness50000 hn ho hc hGRH hL
  · obtain ⟨p, hp, hb, hf⟩ := jointSurplus_global35000 hn ho hc hGRH
    have hmono :=
      jointSurplusCutoff_mono (rho := 130) (R := 30) (by norm_num only)
        (show Real.log n ≤ 340 from le_of_not_ge hL)
    have hr : (155 : ℝ) ≤ jointSurplusRadius 155 29 (Real.log n) := le_max_left _ _
    have hrsq := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 155) hr 2
    have hfloor : (21 / 10 : ℝ) * (155 : ℝ) ^ 2 ≤ jointSurplusCutoff 155 29 (Real.log n) := by
      unfold jointSurplusCutoff
      nlinarith only [hrsq]
    exact ⟨p, hp, ((hb.trans hmono).trans jointSurplus_bridge340.le).trans hfloor, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
