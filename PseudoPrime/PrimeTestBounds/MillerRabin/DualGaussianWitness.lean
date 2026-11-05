/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.DualScaleCore
public import PseudoPrime.PrimeTestBounds.MillerRabin.WideGaussianProfile
public import PseudoPrime.PrimeTestBounds.MillerRabin.EarlyGaussianWitness

/-! # Earlier adaptive Gaussian witness through the dual-scale gap -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The adaptive Gaussian slope stays above a fixed rational lower bound on the new range. -/
theorem dualGaussian_slope_lower (L : ℝ) (hL : 200000000 ≤ L) :
    (3666849 / 10000000 : ℝ) ≤ adaptiveGaussianA L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have h1 : 0 ≤ (61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L :=
    div_nonneg (by norm_num only) (Real.sqrt_nonneg _)
  have h2 : 0 ≤ (39 : ℝ) / L := div_nonneg (by norm_num only) hL0
  dsimp only [adaptiveGaussianA]
  apply (le_div_iff₀ (by norm_num only)).2
  linarith only [h1, h2]

/-- The adaptive Gaussian slope stays below 367/1000 on the new range. -/
theorem dualGaussian_slope_upper (L : ℝ) (hL : 200000000 ≤ L) :
    adaptiveGaussianA L ≤ (367 / 1000 : ℝ) := by
  have hs : (14142 : ℝ) ≤ Real.sqrt L := by
    apply (Real.le_sqrt (by norm_num only) (by linarith only [hL])).2
    nlinarith only [hL]
  have hd :
    (61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L ≤
      (61 / 100 : ℝ) * (28794111 / 12500000) / 14142 := by
    apply div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hs
  have he : (39 : ℝ) / L ≤ 39 / 200000000 := by
    apply div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hL
  dsimp only [adaptiveGaussianA]
  apply (div_le_iff₀ (by norm_num only)).2
  linarith only [hd, he]

/-- The adaptive coefficient exceeds the dual core's fixed square-radius floor. -/
theorem dualGaussian_coeff_lower (L : ℝ) (hL : 200000000 ≤ L) :
    (5313 / 10000 : ℝ) ^ 2 ≤ (21 / 10) * adaptiveGaussianA L ^ 2 := by
  have ha := dualGaussian_slope_lower L hL
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 3666849 / 10000000) ha 2
  nlinarith only [hs]

/-- The adaptive coefficient meets the relative Gaussian profile's upper bound. -/
theorem dualGaussian_coeff_upper (L : ℝ) (hL : 200000000 ≤ L) :
    (21 / 10 : ℝ) * adaptiveGaussianA L ^ 2 ≤ 290762661 / 1000000000 := by
  have ha := dualGaussian_slope_lower L hL
  have hb := dualGaussian_slope_upper L hL
  have hs := pow_le_pow_left₀ (show 0 ≤ adaptiveGaussianA L by linarith only [ha]) hb 2
  nlinarith only [hs]

/-- A rational logarithm certificate places the dual cutoff outside the triangular support. -/
theorem dualGaussian_log36 :
    (36 : ℝ) ≤ Real.log ((5313 / 10000 : ℝ) ^ 2 * (200000000 : ℝ) ^ 2) := by
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 11291187600000000 54 32 36 38 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hc
  norm_num only
  exact hc

/-- The adaptive coefficient satisfies the dual-scale core at the new entrance. -/
noncomputable def dualGaussian_core (L : ℝ) (hL : 200000000 ≤ L) : DualScaleCore where
  C := (21 / 10) * adaptiveGaussianA L ^ 2
  T := 200000000
  a := 5313 / 10000
  v := 14142
  ell := 36
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := dualGaussian_coeff_lower L hL
  upper := by
    have hh := dualGaussian_coeff_upper L hL
    linarith only [hh]
  fourth := by norm_num only [and_self]
  logLower := by
    apply dualGaussian_log36.trans
    apply Real.log_le_log
    · norm_num only
    · exact mul_le_mul_of_nonneg_right (dualGaussian_coeff_lower L hL) (sq_nonneg _)
  margin := by norm_num only [max_eq_right, max_eq_left]

/-- The adaptive coefficient satisfies the relative Gaussian profile at its current scale. -/
noncomputable def dualGaussian_profile (L : ℝ) (hL : 200000000 ≤ L) : WideGaussianProfile where
  C := (21 / 10) * adaptiveGaussianA L ^ 2
  T := L
  a := adaptiveGaussianA L
  v := Real.sqrt L
  entry := hL
  root := by
    have h := dualGaussian_slope_lower L hL
    linarith only [h]
  square := by
    ring_nf
    exact le_rfl
  upper := dualGaussian_coeff_upper L hL
  fourth := by
    have hp : 0 < L := by linarith only [hL]
    exact ⟨Real.sqrt_pos.2 hp, (Real.sq_sqrt hp.le).le⟩
  margin := by
    have hp : 0 < L := by linarith only [hL]
    have hform :
      (10971611 / 5000000 : ℝ) * adaptiveGaussianA L =
        2 * (20115621 / 50000000) + (61 / 100) * (28794111 / 12500000) / Real.sqrt L + 39 / L := by
      unfold adaptiveGaussianA
      ring
    have hdiv : (39 : ℝ) / L * L = 39 := div_mul_cancel₀ _ hp.ne'
    have hmul := congrArg (fun z : ℝ ↦ z * L) hform
    nlinarith only [hmul, hdiv]

/-- Under GRH, every odd composite above scale 200000000 has a rejecting prime below
the adaptive Gaussian cutoff. The dual core and relative Gaussian profile cover
every factor structure. -/
theorem prime_witness_dualGaussian {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (200000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have h36 : 10 ^ 36 ≤ n :=
    decimal_le_of_log_upper (Nat.zero_lt_of_lt hn)
      (by
        norm_num only [Nat.cast_ofNat]
        linarith only [hL])
  have hnlarge : 20000 ≤ n := (by norm_num only : 20000 ≤ 10 ^ 36).trans h36
  apply exists_prime_dualCore (dualGaussian_core (Real.log n) hL) hn ho hc hGRH hL
  intro hsf ht hK hU
  exact
    wideGaussian_witness_card (dualGaussian_profile (Real.log n) hL) ho hsf ht hK hU hnlarge hGRH
      le_rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
