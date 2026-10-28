/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MidscaleWitnessEnvelopes
public import PseudoPrime.PrimeTestBounds.MillerRabin.MidscaleEnvelopeOrder
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaFixedSwitch

/-! # Explicit interval selection -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On 23/2<=L<=120, the two-step cutoff is below 35000.
Its positive radius is less than L-16/5, so a rational square comparison suffices. -/
theorem twoStep_lt_fixed {L : ℝ} (hL : 23 / 2 ≤ L) (hU : L ≤ 120) :
    LLS.PaperStatements.fullEndpointEvenTwoStepCutoff L < 35000 := by
  have hb := LLS.PaperStatements.fullEndpointEvenCorrectionSecondRadius_lt_linear (L := L)
  have hfirst : (8 : ℝ) ≤ LLS.PaperStatements.fullEndpointEvenCorrectionFirstRadius L :=
    le_max_left _ _
  have hsecond := LLS.PaperStatements.fullEndpointEvenCorrectionSecondRadius_gt_first hL
  change LLS.PaperStatements.fullEndpointEvenCorrectionSecondRadius L ^ 2 < 35000
  nlinarith only [hb, hfirst, hsecond, hU]

/-- For n>1 and 23/2<=log n<120, the candidate envelope equals the two-step cutoff.
The cutoff dominates the endpoint base and the fixed 35000 branch throughout this
continuous interval. This proves the single-expression row of the public table. -/
theorem midscale_eq_twoStep_full {n : ℕ} (hn : 1 < n) (hL : 23 / 2 ≤ Real.log n)
    (hU : Real.log n < 120) :
    midscaleWitnessEnvelope n = LLS.PaperStatements.fullEndpointEvenTwoStepCutoff (Real.log n) := by
  have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
  have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
  have h3 : ¬n < 3000 := not_lt.mpr hN
  have h61 : ¬Real.log n ≤ 286 / 25 := by linarith only [hL]
  have hguard : 23 / 2 ≤ Real.log n ∧ Real.log n ≤ 240 := ⟨hL, by linarith only [hU]⟩
  have hbase := twoStep_lt_endpoint hL (by linarith only [hU])
  have hfixed := twoStep_lt_fixed hL hU.le
  simp only [midscaleWitnessEnvelope, mrTwoStepEnvelope, ite_eq_left hguard, mrLowBase,
    ite_eq_right h2, ite_eq_right h3, mrAnalyticBase, ite_eq_right h61, ite_eq_left hU,
    min_eq_right hbase.le]
  split_ifs
  · exact min_eq_left hfixed.le
  · rfl

/-- For n>1 and 120<=log n<=the exact switch, the candidate envelope equals the refined
1000-prefix Gamma bound. It dominates the endpoint overlap and the two-step cutoff;
the fixed value and 35000-prefix floor are no smaller. -/
theorem midscale_eq_gamma {n : ℕ} (hn : 1 < n) (hL : 120 ≤ Real.log n)
    (hS : Real.log n ≤ gammaFixedSwitch) :
    midscaleWitnessEnvelope n = gamma1000RefinedBound (Real.log n) := by
  have h240 : Real.log n < 240 := by linarith only [hS, gammaFixedSwitch_bounds.2]
  have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
  have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
  have h3 : ¬n < 3000 := not_lt.mpr hN
  have h61 : ¬Real.log n ≤ 286 / 25 := by linarith only [hL]
  have he : ¬Real.log n < 120 := not_lt.mpr hL
  have hg := gammaRefined_le_fixed hL hS
  have hg35 := hg.trans (gamma35000_floor (Real.log n))
  have hc2 := gamma_lt_twoStep hL h240.le
  have hguard : 23 / 2 ≤ Real.log n ∧ Real.log n ≤ 240 := ⟨by linarith only [hL], h240.le⟩
  have hfixed : 63 ≤ Real.log n ∧ Real.log n ≤ 240 := ⟨by linarith only [hL], h240.le⟩
  simp only [midscaleWitnessEnvelope, ite_eq_left hfixed, mrTwoStepEnvelope, ite_eq_left hguard,
    mrLowBase, ite_eq_right h2, ite_eq_right h3, mrAnalyticBase, ite_eq_right h61, ite_eq_right he,
    gammaLowEnvelope, min_eq_right hg35, ite_eq_left h240]
  by_cases h122 : Real.log n ≤ 122
  · have hend := hc2.trans (twoStep_lt_endpoint hguard.1 h122)
    simp only [ite_eq_left h122, min_eq_right hend.le, min_eq_left hc2.le, min_eq_left hg]
  · simp only [ite_eq_right h122, min_eq_left hc2.le, min_eq_left hg]

/-- For n>1 and switch<=log n<=240, the candidate envelope equals 35000.
The fixed value dominates both Gamma branches and the two-step cutoff. At 240
the separate Gaussian B6 comparison removes the endpoint candidate as well. -/
theorem midscale_eq_fixed {n : ℕ} (hn : 1 < n) (hS : gammaFixedSwitch ≤ Real.log n)
    (hU : Real.log n ≤ 240) : midscaleWitnessEnvelope n = 35000 := by
  have hL : 120 ≤ Real.log n := by linarith only [hS, gammaFixedSwitch_bounds.1]
  have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
  have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
  have h3 : ¬n < 3000 := not_lt.mpr hN
  have h61 : ¬Real.log n ≤ 286 / 25 := by linarith only [hL]
  have he : ¬Real.log n < 120 := not_lt.mpr hL
  have h122 : ¬Real.log n ≤ 122 := by linarith only [hS, gammaFixedSwitch_bounds.1]
  have hg := fixed_le_gammaRefined hL hS
  have hg35 := gamma35000_floor (Real.log n)
  have hc2 := hg.trans (gamma_lt_twoStep hL hU).le
  have hguard : 23 / 2 ≤ Real.log n ∧ Real.log n ≤ 240 := ⟨by linarith only [hL], hU⟩
  have hfixed : 63 ≤ Real.log n ∧ Real.log n ≤ 240 := ⟨by linarith only [hL], hU⟩
  simp only [midscaleWitnessEnvelope, ite_eq_left hfixed, mrTwoStepEnvelope, ite_eq_left hguard,
    mrLowBase, ite_eq_right h2, ite_eq_right h3, mrAnalyticBase, ite_eq_right h61, ite_eq_right he,
    ite_eq_right h122]
  apply min_eq_right
  apply le_min _ hc2
  by_cases h240 : Real.log n < 240
  · simp only [ite_eq_left h240, gammaLowEnvelope]
    exact le_min hg35 hg
  · have heq : Real.log n = 240 := le_antisymm hU (le_of_not_gt h240)
    simp only [ite_eq_right h240,
      gaussianMRWitnessEnvelope_eq240 (by linarith only [heq]) (by linarith only [heq])]
    exact (Analysis.gaussianMR6_prefix35000 (by linarith only [heq])).le

/-- The explicit interval envelope for the least prime rejecting strong MR.
Integer guards select two and three; logarithmic guards select 61, the shifted
quadratic, the two-step cutoff, refined Gamma, fixed 35000, and the high envelope.
The exact Gamma switch prevents a rounded boundary and no midscale minimum remains. -/
noncomputable def selectedWitnessEnvelope (n : ℕ) : ℝ :=
  let L := Real.log n
  if n < 2047 then 2
  else
    if n < 3000 then 3
    else
      if L ≤ 286 / 25 then 61
      else
        if L < 23 / 2 then (64 / 81 : ℝ) * (L - 7 / 4) ^ 2
        else
          if L < 120 then LLS.PaperStatements.fullEndpointEvenTwoStepCutoff L
          else
            if L ≤ gammaFixedSwitch then gamma1000RefinedBound L
            else if L ≤ 240 then 35000 else gaussianMRWitnessEnvelope n

/-- For every n>1, the candidate minimum equals the explicit selected envelope.
Use continuous dominance theorems on every analytic interval and simplify the finite
guards. This equality certifies that the public interval selection loses no candidate. -/
theorem midscale_eq_selected {n : ℕ} (hn : 1 < n) :
    midscaleWitnessEnvelope n = selectedWitnessEnvelope n := by
  have hsmall : n < 3000 → Real.log n < 11 := by
    intro h
    have hN : (n : ℝ) ≤ 46000 := by exact_mod_cast (h.le.trans (by norm_num only))
    exact
      (Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)) hN).trans_lt
        Analysis.log_46000_lt_eleven
  by_cases h2 : n < 2047
  · have h3 : n < 3000 := h2.trans (by norm_num only)
    have hL := hsmall h3
    have hg : ¬(23 / 2 ≤ Real.log n ∧ Real.log n ≤ 240) := by
      intro h
      linarith only [h.1, hL]
    have hf : ¬(63 ≤ Real.log n ∧ Real.log n ≤ 240) := by
      intro h
      linarith only [h.1, hL]
    simp only [selectedWitnessEnvelope, ite_eq_left h2, midscaleWitnessEnvelope, ite_eq_right hf,
      mrTwoStepEnvelope, ite_eq_right hg, mrLowBase]
  · by_cases h3 : n < 3000
    · have hL := hsmall h3
      have hg : ¬(23 / 2 ≤ Real.log n ∧ Real.log n ≤ 240) := by
        intro h
        linarith only [h.1, hL]
      have hf : ¬(63 ≤ Real.log n ∧ Real.log n ≤ 240) := by
        intro h
        linarith only [h.1, hL]
      simp only [selectedWitnessEnvelope, midscaleWitnessEnvelope, ite_eq_right hf,
        mrTwoStepEnvelope, ite_eq_right hg, mrLowBase, ite_eq_right h2, ite_eq_left h3]
    · simp only [selectedWitnessEnvelope, ite_eq_right h2, ite_eq_right h3]
      by_cases h61 : Real.log n ≤ 286 / 25
      · have hg : ¬(23 / 2 ≤ Real.log n ∧ Real.log n ≤ 240) := by
          intro h
          linarith only [h.1, h61]
        have hf : ¬(63 ≤ Real.log n ∧ Real.log n ≤ 240) := by
          intro h
          linarith only [h.1, h61]
        simp only [midscaleWitnessEnvelope, ite_eq_right hf, mrTwoStepEnvelope, ite_eq_right hg,
          mrLowBase, ite_eq_right h2, ite_eq_right h3, mrAnalyticBase, ite_eq_left h61]
      · rw [ite_eq_right h61]
        by_cases h23 : Real.log n < 23 / 2
        · have hg : ¬(23 / 2 ≤ Real.log n ∧ Real.log n ≤ 240) := by
            intro h
            linarith only [h.1, h23]
          have hf : ¬(63 ≤ Real.log n ∧ Real.log n ≤ 240) := by
            intro h
            linarith only [h.1, h23]
          have he : Real.log n < 120 := by linarith only [h23]
          have h22 : Real.log n ≤ 22 := by linarith only [h23]
          simp only [ite_eq_left h23, midscaleWitnessEnvelope, ite_eq_right hf, mrTwoStepEnvelope,
            ite_eq_right hg, mrLowBase, ite_eq_right h2, ite_eq_right h3, mrAnalyticBase,
            ite_eq_right h61, ite_eq_left he, endpointMidscaleBase, ite_eq_left h22]
        · rw [ite_eq_right h23]
          by_cases h120 : Real.log n < 120
          · rw [ite_eq_left h120]
            exact midscale_eq_twoStep_full hn (le_of_not_gt h23) h120
          · rw [ite_eq_right h120]
            by_cases hS : Real.log n ≤ gammaFixedSwitch
            · rw [ite_eq_left hS]
              exact midscale_eq_gamma hn (le_of_not_gt h120) hS
            · rw [ite_eq_right hS]
              by_cases h240 : Real.log n ≤ 240
              · rw [ite_eq_left h240]
                exact midscale_eq_fixed hn (le_of_not_ge hS) h240
              · rw [ite_eq_right h240]
                exact midscaleWitnessEnvelope_eq_high hn (lt_of_not_ge h240)

/-- Under GRH, every odd composite n>1 has a least prime rejecting strong MR at most
the explicit interval envelope. Transfer the all-input least-witness theorem through
the proved selection equality; no factorization or subgroup restrictions are exposed. -/
theorem exists_least_selectedWitness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ selectedWitnessEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  rw [← midscale_eq_selected hn]
  exact exists_least_midscaleWitness hn ho hc hGRH

/-- Under GRH, every odd composite n>1 has a prime rejecting strong MR within the
explicit interval envelope. Transfer the actual witness theorem through the selection
equality, retaining primality, the numeric bound, and rejection. -/
theorem exists_prime_selectedWitness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ selectedWitnessEnvelope n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rw [← midscale_eq_selected hn]
  exact exists_prime_midscaleWitness hn ho hc hGRH

end PseudoPrime.PrimeTestBounds.MillerRabin
