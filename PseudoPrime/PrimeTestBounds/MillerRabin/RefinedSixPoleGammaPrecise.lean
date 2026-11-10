/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleGammaSecond
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedDigammaSquarePrefix
public import PseudoPrime.AnalyticNumberTheory.Gamma.RealDigammaTrapezoid
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.Analysis.PrecisePiLogBound

/-! # Sharper sixth-pole even Gamma bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Sixteen reciprocal terms and the digamma trapezoid bound show that
digamma at `79/100` is below `-9879/10000`. -/
theorem refined_digamma_point_precise : digammaReal (79 / 100) < -(9879 / 10000 : ℝ) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck (1679 / 100) 4 32 0 (282079 / 100000) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have h :=
    (AnalyticNumberTheory.Gamma.real_digamma_finite_prefix_bounds (r := (79 / 100 : ℝ))
        (by norm_num only) 16).2
  norm_num only [digammaReal, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at h ⊢
  linarith only [h, hlog]

/-- A checked reciprocal-square prefix gives a lower bound for the real
digamma derivative at `79/100`. Its independent blocks are reused. -/
theorem refined_digamma_first_precise : (234 / 100 : ℝ) < deriv digammaReal (79 / 100) := by
  have hu : (1 / 2 : ℝ) < 79 / 100 := by norm_num only
  have hd := digammaReal_hasDeriv hu
  have h := digamma_deriv_ge_prefix (by norm_num only : (0 : ℝ) < 79 / 100) hd 256
  rw [hd.deriv]
  exact refined_digamma_square_prefix.trans_le h

/-- Sixteen positive reciprocal-cube terms bound the second real digamma
derivative at `79/100` from above. -/
theorem refined_digamma_second_precise :
    deriv (deriv digammaReal) (79 / 100) < -(4583 / 1000 : ℝ) := by
  have hu : (1 / 2 : ℝ) < 79 / 100 := by norm_num only
  have hp : Summable (fun n : ℕ ↦ (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr (by norm_num only : (1 : ℝ) < 2))
    simpa only [Nat.cast_add, Nat.cast_one, Real.rpow_two] using h
  have hpos (n : ℕ) : 0 ≤ 2 * ((79 / 100 : ℝ) + n)⁻¹ ^ 3 := by positivity
  have hs : Summable (fun n : ℕ ↦ 2 * ((79 / 100 : ℝ) + n)⁻¹ ^ 3) := by
    apply (hp.mul_left 16).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (hpos n), ← inv_pow]
    exact inv_shift_cub_bound hu n
  have hsum := hs.sum_le_tsum (Finset.range 16) (fun n _ ↦ hpos n)
  have hd := (digammaReal_second_series hu).deriv
  rw [show
      (fun n : ℕ ↦ -2 * ((79 / 100 : ℝ) + n)⁻¹ ^ 3) =
        (fun n : ℕ ↦ -(2 * ((79 / 100 : ℝ) + n)⁻¹ ^ 3))
      from funext (fun n ↦ by ring),
    tsum_neg] at hd
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one] at hsum
  linarith only [hsum, hd]

/-- The second even Gamma derivative inherits the improved real digamma bound. -/
theorem refined_gamma_even_second_precise {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Even) :
    deriv (deriv (fun u : ℝ ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re)) (27 / 25) <
      -(4583 / 8000 : ℝ) := by
  have ha : (1 / 2 : ℝ) < 27 / 25 := by norm_num only
  have hz : (1 / 2 : ℝ) < 79 / 100 := by norm_num only
  have hc : (((1 / 2 : ℝ) + 27 / 25) / 2 : ℝ) = 79 / 100 := by norm_num only
  have heq :
    deriv
        (fun u : ℝ ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re) =ᶠ[nhds (27 / 25 : ℝ)]
      (fun u : ℝ ↦ deriv digammaReal (((1 / 2 : ℝ) + u) / 2) / 4) := by
    filter_upwards [Ioi_mem_nhds ha] with u hu
    exact gamma_even_deriv_identity he hu
  have hd := digammaReal_second_series hz
  rw [← hc] at hd
  have hd' :=
    (hd.comp (27 / 25 : ℝ)
          (((hasDerivAt_id (27 / 25 : ℝ)).const_add (1 / 2 : ℝ)).div_const 2)).div_const
      4
  simp only [Function.comp_def, id_eq, hc] at hd'
  have hnum := refined_digamma_second_precise
  have hsecond : deriv (deriv digammaReal) (79 / 100) = ∑' n : ℕ, -2 * ((79 / 100 : ℝ) + n)⁻¹ ^ 3 :=
    (digammaReal_second_series hz).deriv
  rw [heq.deriv_eq, hd'.deriv]
  linarith only [hnum, hsecond]

/-- The even sixth-pole Gamma correction is bounded using the sharper point
and derivative estimates. The numerical constant remains independent of the character. -/
theorem refined_gamma_even_precise {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (he : χ.Even) :
    sixGamma χ < -(98 / 25 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have hpoint :=
    AnalyticNumberTheory.DirichletLFunction.re_gammaFactor_even he (σ := (1 / 2 : ℝ) + 27 / 25)
      (by norm_num only)
  have hc : (((1 / 2 : ℝ) + 27 / 25) / 2 : ℝ) = 79 / 100 := by norm_num only
  rw [hc] at hpoint
  have h0 : (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + 27 / 25 : ℝ) : ℂ)).re < -(5331 / 5000 : ℝ) := by
    have hd := refined_digamma_point_precise
    dsimp only [digammaReal] at hd
    have hp := Analysis.log_pi_ge_2096_div_1831
    linarith only [hpoint, hd, hp]
  have hfirst := gamma_even_deriv_identity he (u := (27 / 25 : ℝ)) (by norm_num only)
  rw [hc] at hfirst
  have h1 :
    (234 / 400 : ℝ) <
      deriv (fun u : ℝ ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re) (27 / 25) := by
    rw [hfirst]
    linarith only [refined_digamma_first_precise]
  have h2 := refined_gamma_even_second_precise he
  unfold sixGamma
  norm_num only at h0 h1 h2 ⊢
  linarith only [h0, h1, h2]

end PseudoPrime.PrimeTestBounds.MillerRabin
