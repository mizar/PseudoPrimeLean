/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.DualScaleComparison

/-! # Continuous dual-scale and Gaussian witness coefficient -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The nonnegative profile majorant used by the continuous dual-scale radius. -/
noncomputable def smoothDual_shift (L : ℝ) : ℝ :=
  36 + max 0 (36 + Real.log 4 - 2 * Real.log L)

/-- The explicit safe dual-scale radius with a strict unit margin. -/
noncomputable def smoothDual_radius (L : ℝ) : ℝ :=
  (smoothDual_shift L + (1456 + 13 / 10000000) / Real.sqrt L + 12066 / L) / (68 - 3 / 10000)

/-- The explicit Gaussian radius with a strict unit margin. -/
noncomputable def smoothGaussian_radius (L : ℝ) : ℝ :=
  (161 / 200 + (238 / 5) / Real.sqrt L + 91 / L) / (21943 / 10000)

/-- The larger squared cutoff needed by the dual and Gaussian branches. -/
noncomputable def smoothCoeff (L : ℝ) : ℝ :=
  max (smoothDual_radius L ^ 2) ((21 / 10) * smoothGaussian_radius L ^ 2)

/-- A rational logarithm certificate bounds the logarithmic scale below. -/
theorem smooth_log_lower (L : ℝ) (hL : 5000000 ≤ L) : (77 / 5 : ℝ) ≤ Real.log L := by
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 5000000 23 32 (77 / 5) 16 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  exact hc.trans (Real.log_le_log (by norm_num only) hL)

/-- The continuous dual radius lies between rational bounds above its entrance. -/
theorem smoothDual_radius_bounds (L : ℝ) (hL : 5000000 ≤ L) :
    (9 / 17 : ℝ) ≤ smoothDual_radius L ∧ smoothDual_radius L ≤ 16 / 25 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hs : (2236 : ℝ) ≤ Real.sqrt L := by
    apply (Real.le_sqrt (by norm_num only) hL0.le).2
    nlinarith only [hL]
  have hs0 : 0 < Real.sqrt L := by linarith only [hs]
  have hlog := smooth_log_lower L hL
  have hlog4 : Real.log 4 ≤ (7 / 5 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    nlinarith only [Real.log_two_lt_d9]
  have hm0 : 0 ≤ max (0 : ℝ) (36 + Real.log 4 - 2 * Real.log L) := le_max_left _ _
  have hm8 : max (0 : ℝ) (36 + Real.log 4 - 2 * Real.log L) ≤ 33 / 5 := by
    apply max_le (by norm_num only)
    linarith only [hlog, hlog4]
  have h1 : 0 ≤ (1456 + 13 / 10000000 : ℝ) / Real.sqrt L := div_nonneg (by norm_num only) hs0.le
  have h2 : 0 ≤ (12066 : ℝ) / L := div_nonneg (by norm_num only) hL0.le
  have h1u : (1456 + 13 / 10000000 : ℝ) / Real.sqrt L ≤ (1456 + 13 / 10000000 : ℝ) / 2236 :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hs
  have h2u : (12066 : ℝ) / L ≤ 12066 / 5000000 :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hL
  unfold smoothDual_radius smoothDual_shift
  constructor
  · apply (le_div_iff₀ (by norm_num only)).2
    nlinarith only [hm0, h1, h2]
  · apply (div_le_iff₀ (by norm_num only)).2
    nlinarith only [hm8, h1u, h2u]

/-- The Gaussian radius has a rational upper bound above the entrance. -/
theorem smoothGaussian_radius_upper (L : ℝ) (hL : 5000000 ≤ L) :
    smoothGaussian_radius L ≤ 19 / 50 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hs : (2236 : ℝ) ≤ Real.sqrt L := by
    apply (Real.le_sqrt (by norm_num only) hL0.le).2
    nlinarith only [hL]
  have h1u : (238 / 5 : ℝ) / Real.sqrt L ≤ (238 / 5 : ℝ) / 2236 :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hs
  have h2u : (91 : ℝ) / L ≤ 91 / 5000000 :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hL
  unfold smoothGaussian_radius
  apply (div_le_iff₀ (by norm_num only)).2
  linarith only [h1u, h2u]

/-- The Gaussian radius is positive above the entrance. -/
theorem smoothGaussian_radius_pos (L : ℝ) (hL : 5000000 ≤ L) : 0 < smoothGaussian_radius L := by
  have hL0 : 0 < L := by linarith only [hL]
  have h1 : 0 ≤ (238 / 5 : ℝ) / Real.sqrt L := div_nonneg (by norm_num only) (Real.sqrt_nonneg _)
  have h2 : 0 ≤ (91 : ℝ) / L := div_nonneg (by norm_num only) hL0.le
  unfold smoothGaussian_radius
  apply (div_pos_iff_of_pos_right (by norm_num only)).2
  linarith only [h1, h2]

/-- The combined continuous coefficient lies between one quarter and four ninths. -/
theorem smoothCoeff_bounds (L : ℝ) (hL : 5000000 ≤ L) :
    (1 / 4 : ℝ) ≤ smoothCoeff L ∧ smoothCoeff L ≤ 4 / 9 := by
  have ha := smoothDual_radius_bounds L hL
  have hb := smoothGaussian_radius_upper L hL
  have hb0 := smoothGaussian_radius_pos L hL
  have ha2 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 9 / 17) ha.1 2
  have haU := pow_le_pow_left₀ (by linarith only [ha.1]) ha.2 2
  have hbU := pow_le_pow_left₀ hb0.le hb 2
  unfold smoothCoeff
  constructor
  · exact
      (by nlinarith only [ha2] : (1 / 4 : ℝ) ≤ smoothDual_radius L ^ 2) |>.trans (le_max_left _ _)
  · apply max_le
    · nlinarith only [haU]
    · nlinarith only [hbU]

/-- The continuous cutoff is at least the logarithmic profile floor. -/
theorem smooth_log_cutoff (L : ℝ) (hL : 5000000 ≤ L) :
    2 * Real.log L - Real.log 4 ≤ Real.log (smoothCoeff L * L ^ 2) := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc := (smoothCoeff_bounds L hL).1
  have hbase : (1 / 4 : ℝ) * L ^ 2 ≤ smoothCoeff L * L ^ 2 :=
    mul_le_mul_of_nonneg_right hc (sq_nonneg L)
  have hp : 0 < (1 / 4 : ℝ) * L ^ 2 := mul_pos (by norm_num only) (sq_pos_of_pos hL0)
  have hh := Real.log_le_log hp hbase
  rw [Real.log_mul (by norm_num only) (pow_ne_zero _ hL0.ne'), Real.log_pow] at hh
  have hi : Real.log (1 / 4 : ℝ) = -Real.log 4 := by rw [one_div, Real.log_inv]
  rw [hi] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh]

/-- The continuous cutoff satisfies the dual core at the current scale. -/
noncomputable def smoothDual_core (L : ℝ) (hL : 5000000 ≤ L) : DualScaleCore where
  C := smoothCoeff L
  T := L
  a := smoothDual_radius L
  v := Real.sqrt L
  ell := 2 * Real.log L - Real.log 4
  entry := by linarith only [hL]
  root := by
    have hh := (smoothDual_radius_bounds L hL).1
    linarith only [hh]
  localBudget := by
    have hh := (smoothDual_radius_bounds L hL).1
    nlinarith only [hh, hL,
      mul_nonneg (show (0 : ℝ) ≤ smoothDual_radius L - 9 / 17 by linarith only [hh])
        (show (0 : ℝ) ≤ L by linarith only [hL])]
  square := le_max_left _ _
  upper := by
    have hh := (smoothCoeff_bounds L hL).2
    linarith only [hh]
  fourth := by
    have hp : 0 < L := by linarith only [hL]
    exact ⟨Real.sqrt_pos.2 hp, (Real.sq_sqrt hp.le).le⟩
  logLower := smooth_log_cutoff L hL
  margin := by
    have hp : 0 < L := by linarith only [hL]
    have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hp
    have hform :
      (68 - 3 / 10000 : ℝ) * smoothDual_radius L =
        smoothDual_shift L + (1456 + 13 / 10000000 : ℝ) / Real.sqrt L + 12066 / L := by
      unfold smoothDual_radius
      ring
    have heq : smoothDual_shift L = 36 + max 0 (36 - (2 * Real.log L - Real.log 4)) := by
      unfold smoothDual_shift
      congr 1
      congr 1
      ring
    rw [heq] at hform
    have hdiv : (12066 : ℝ) / L * L = 12066 := div_mul_cancel₀ _ hp.ne'
    have hmul := congrArg (fun z : ℝ ↦ z * L) hform
    nlinarith only [hmul, hdiv]

/-- On the finite bridge the Gaussian radius exceeds the required floor. -/
theorem smoothGaussian_radius_lower (L : ℝ) (hL : 5000000 ≤ L) (hU : L ≤ 200000000) :
    (367 / 1000 : ℝ) ≤ smoothGaussian_radius L := by
  have hL0 : 0 < L := by linarith only [hL]
  have hs : Real.sqrt L ≤ (14143 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num only
    · nlinarith only [hU]
  have hs0 : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
  have h1 : (238 / 5 : ℝ) / 14143 ≤ (238 / 5 : ℝ) / Real.sqrt L :=
    div_le_div_of_nonneg_left (by norm_num only) hs0 hs
  have h2 : 0 ≤ (91 : ℝ) / L := div_nonneg (by norm_num only) hL0.le
  unfold smoothGaussian_radius
  apply (le_div_iff₀ (by norm_num only)).2
  linarith only [h1, h2]

/-- The combined cutoff satisfies the Gaussian triple profile on the bridge. -/
noncomputable def smoothGaussian_profile (L : ℝ) (hL : 5000000 ≤ L) (hU : L ≤ 200000000) :
    ReducedGaussianProfile
    where
  C := smoothCoeff L
  T := L
  gamma := smoothGaussian_radius L
  v := Real.sqrt L
  entry := by linarith only [hL]
  gammaLower := smoothGaussian_radius_lower L hL hU
  lower := by
    have hh : (21 / 10 : ℝ) * smoothGaussian_radius L ^ 2 ≤ smoothCoeff L := le_max_right _ _
    linarith only [hh]
  upper := by
    have hh := (smoothCoeff_bounds L hL).2
    linarith only [hh]
  fourth := by
    have hp : 0 < L := by linarith only [hL]
    exact ⟨Real.sqrt_pos.2 hp, (Real.sq_sqrt hp.le).le⟩
  margin := by
    have hp : 0 < L := by linarith only [hL]
    have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hp
    have hform :
      (21943 / 10000 : ℝ) * smoothGaussian_radius L =
        161 / 200 + (238 / 5 : ℝ) / Real.sqrt L + 91 / L := by
      unfold smoothGaussian_radius
      ring
    have hdiv : (91 : ℝ) / L * L = 91 := div_mul_cancel₀ _ hp.ne'
    have hmul := congrArg (fun z : ℝ ↦ z * L) hform
    nlinarith only [hmul, hdiv]

/-- Under GRH, the continuous cutoff gives an actual rejecting prime on the finite bridge. -/
theorem prime_witness_smoothDual {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (5000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 200000000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ smoothCoeff (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_dualCore (smoothDual_core (Real.log n) hL) hn ho hc hGRH le_rfl
  intro hsf ht hK hU'
  exact
    reducedGaussian_cardWitness (smoothGaussian_profile (Real.log n) hL hU) ho hsf ht hK hU' hGRH
      le_rfl

/-- The dual profile majorant is nonincreasing above the entrance. -/
theorem smoothDual_shift_anti {L M : ℝ} (hL : 5000000 ≤ L) (hLM : L ≤ M) :
    smoothDual_shift M ≤ smoothDual_shift L := by
  have hlog := Real.log_le_log (by linarith only [hL]) hLM
  unfold smoothDual_shift
  have hh : 36 + Real.log 4 - 2 * Real.log M ≤ 36 + Real.log 4 - 2 * Real.log L := by
    linarith only [hlog]
  exact add_le_add_right (max_le_max_left 0 hh) 36

/-- The continuous dual radius is nonincreasing above the entrance. -/
theorem smoothDual_radius_anti {L M : ℝ} (hL : 5000000 ≤ L) (hLM : L ≤ M) :
    smoothDual_radius M ≤ smoothDual_radius L := by
  have hL0 : 0 < L := by linarith only [hL]
  have hs : Real.sqrt L ≤ Real.sqrt M := Real.sqrt_le_sqrt hLM
  have h1 : (1456 + 13 / 10000000 : ℝ) / Real.sqrt M ≤ (1456 + 13 / 10000000 : ℝ) / Real.sqrt L :=
    div_le_div_of_nonneg_left (by norm_num only) (Real.sqrt_pos.2 hL0) hs
  have h2 : (12066 : ℝ) / M ≤ 12066 / L := div_le_div_of_nonneg_left (by norm_num only) hL0 hLM
  unfold smoothDual_radius
  apply (div_le_div_iff_of_pos_right (by norm_num only)).2
  have hd := smoothDual_shift_anti hL hLM
  linarith only [h1, h2, hd]

/-- The continuous Gaussian radius is nonincreasing above the entrance. -/
theorem smoothGaussian_radius_anti {L M : ℝ} (hL : 5000000 ≤ L) (hLM : L ≤ M) :
    smoothGaussian_radius M ≤ smoothGaussian_radius L := by
  have hL0 : 0 < L := by linarith only [hL]
  have hs : Real.sqrt L ≤ Real.sqrt M := Real.sqrt_le_sqrt hLM
  have h1 : (238 / 5 : ℝ) / Real.sqrt M ≤ (238 / 5 : ℝ) / Real.sqrt L :=
    div_le_div_of_nonneg_left (by norm_num only) (Real.sqrt_pos.2 hL0) hs
  have h2 : (91 : ℝ) / M ≤ 91 / L := div_le_div_of_nonneg_left (by norm_num only) hL0 hLM
  unfold smoothGaussian_radius
  apply (div_le_div_iff_of_pos_right (by norm_num only)).2
  linarith only [h1, h2]

/-- The combined normalized coefficient is nonincreasing above the entrance. -/
theorem smoothCoeff_anti {L M : ℝ} (hL : 5000000 ≤ L) (hLM : L ≤ M) :
    smoothCoeff M ≤ smoothCoeff L := by
  have hM : 5000000 ≤ M := hL.trans hLM
  have ha :=
    pow_le_pow_left₀ (by linarith only [(smoothDual_radius_bounds M hM).1])
      (smoothDual_radius_anti hL hLM) 2
  have hb :=
    pow_le_pow_left₀ (smoothGaussian_radius_pos M hM).le (smoothGaussian_radius_anti hL hLM) 2
  unfold smoothCoeff
  exact max_le_max ha (mul_le_mul_of_nonneg_left hb (by norm_num only))

end PseudoPrime.PrimeTestBounds.MillerRabin
