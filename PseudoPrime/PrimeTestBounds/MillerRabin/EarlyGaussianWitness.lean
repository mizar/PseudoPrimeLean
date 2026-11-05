/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAdaptiveProfile
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedContourWitness

/-! # Earlier entrance for the adaptive Gaussian witness -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Above scale thirty billion, the adaptive Gaussian slope exceeds a fixed rational lower bound. -/
theorem earlyGaussian_slope_lower (L : ℝ) (hL : 30000000000 ≤ L) :
    (3666849 / 10000000 : ℝ) ≤ adaptiveGaussianA L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have h1 : 0 ≤ (61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L :=
    div_nonneg (by norm_num only) (Real.sqrt_nonneg _)
  have h2 : 0 ≤ (39 : ℝ) / L := div_nonneg (by norm_num only) hL0
  dsimp only [adaptiveGaussianA]
  apply (le_div_iff₀ (by norm_num only)).2
  linarith only [h1, h2]
/-- Above scale thirty billion, the adaptive Gaussian slope is at most `36669 / 100000`. -/
theorem earlyGaussian_slope_upper (L : ℝ) (hL : 30000000000 ≤ L) :
    adaptiveGaussianA L ≤ (36669 / 100000 : ℝ) := by
  have hs : (173205 : ℝ) ≤ Real.sqrt L := by
    apply (Real.le_sqrt (by norm_num only) (by linarith only [hL])).2
    nlinarith only [hL]
  have hd : (61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L ≤
      (61 / 100 : ℝ) * (28794111 / 12500000) / 173205 := by
    apply div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hs
  have he : (39 : ℝ) / L ≤ 39 / 30000000000 := by
    apply div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hL
  dsimp only [adaptiveGaussianA]
  apply (div_le_iff₀ (by norm_num only)).2
  linarith only [hd, he]
/-- Above the early entrance, the Gaussian coefficient dominates the reduced
triangular radius floor. -/
theorem earlyGaussian_coeff_lower (L : ℝ) (hL : 30000000000 ≤ L) :
    (5313 / 10000 : ℝ) ^ 2 ≤ (21 / 10) * adaptiveGaussianA L ^ 2 := by
  have ha := earlyGaussian_slope_lower L hL
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 3666849 / 10000000) ha 2
  nlinarith only [hs]
/-- Above the early entrance, the Gaussian coefficient is strictly below `28237 / 100000`. -/
theorem earlyGaussian_coeff_upper (L : ℝ) (hL : 30000000000 ≤ L) :
    (21 / 10 : ℝ) * adaptiveGaussianA L ^ 2 < 28237 / 100000 := by
  have ha := earlyGaussian_slope_lower L hL
  have hb := earlyGaussian_slope_upper L hL
  have hs := pow_le_pow_left₀ (show 0 ≤ adaptiveGaussianA L by linarith only [ha]) hb 2
  nlinarith only [hs]
/-- At each eligible scale the adaptive Gaussian coefficient satisfies the
reduced triangular core. -/
noncomputable def earlyGaussian_core (L : ℝ) (hL : 30000000000 ≤ L) : ReducedContourCore where
  C := (21 / 10) * adaptiveGaussianA L ^ 2
  T := 30000000000
  a := 5313 / 10000
  m := 377 / 20
  v := 173205
  b := 26659 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := earlyGaussian_coeff_lower L hL
  upper := by
    have h := earlyGaussian_coeff_upper L hL
    linarith only [h]
  root16 := by
    constructor
    · norm_num only
    · have ha := earlyGaussian_slope_lower L hL
      have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 3666849 / 10000000) ha 2
      nlinarith only [hs]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  margin := by norm_num only
/-- At each eligible scale the adaptive coefficient defines a relative Gaussian triple profile. -/
noncomputable def earlyGaussian_profile (L : ℝ) (hL : 30000000000 ≤ L) :
    GaussianRelativeProfile where
  C := (21 / 10) * adaptiveGaussianA L ^ 2
  T := L
  a := adaptiveGaussianA L
  v := Real.sqrt L
  entry := hL
  root := by
    have h := earlyGaussian_slope_lower L hL
    linarith only [h]
  square := by
    ring_nf
    exact le_rfl
  upper := (earlyGaussian_coeff_upper L hL).le
  fourth := by
    have hp : 0 < L := by linarith only [hL]
    exact ⟨Real.sqrt_pos.2 hp, (Real.sq_sqrt hp.le).le⟩
  margin := by
    have hp : 0 < L := by linarith only [hL]
    have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hp
    dsimp only [adaptiveGaussianA]
    field_simp [hp.ne', hs.ne']
    nlinarith only [hp, hs]
/-- Under GRH, every odd composite with logarithm at least thirty billion has a rejecting
prime below the adaptive Gaussian cutoff. The reduced core and relative Gaussian profile
cover the local, large-index and triple branches. -/
theorem prime_witness_earlyGaussian {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (30000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧
      (p : ℝ) ≤ ((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have h36 : 10 ^ 36 ≤ n := decimal_le_of_log_upper (Nat.zero_lt_of_lt hn) (by
    norm_num only [Nat.cast_ofNat]
    linarith only [hL])
  have hnlarge : 20000 ≤ n := (by norm_num only : 20000 ≤ 10 ^ 36).trans h36
  apply exists_prime_reducedCore (earlyGaussian_core (Real.log n) hL) hn ho hc hGRH hL
  intro hsf ht hK hU
  exact gaussianProfile_witness_card (earlyGaussian_profile (Real.log n) hL) ho hsf ht hK hU
    hnlarge hGRH le_rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
