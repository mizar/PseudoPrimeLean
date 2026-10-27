/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaEulerTailErrorCertificate
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedDifferences

/-! # Coarse RH arithmetic inputs for the finite Euler mass center -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH, the actual logarithmically weighted Mangoldt error
is at most 35 throughout [1,50000]. Apply the sharp global error bound,
then bound the square root by 225 and logarithm by twelve. -/
theorem gamma_smoothed_error_le_thirty_five (hRH : RiemannHypothesis) {t : ℝ} (ht : 1 ≤ t)
    (hb : t ≤ 50000) : |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t| ≤ 35 := by
  have he := logWeightedMangoldtSum_error_le_refined_global hRH (zero_lt_one.trans_le ht)
  rw [max_eq_right ht] at he
  have hs : Real.sqrt t ≤ 225 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num only, hb.trans (by norm_num only : (50000 : ℝ) ≤ 225 ^ 2)⟩
  have hl := (Real.log_le_log (zero_lt_one.trans_le ht) hb).trans gamma_tail_log_cutoff_le
  linarith only [he, hs, hl]

/-- Under RH, the actual logarithmically weighted Mangoldt sum
at 50000 is at least 49965. Use the lower side of the certified absolute
error bound. This supplies the negative-slope center comparison. -/
theorem gamma_smoothed_cutoff_lower (hRH : RiemannHypothesis) :
    (49965 : ℝ) ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 50000 := by
  have he :=
    abs_le.mp (gamma_smoothed_error_le_thirty_five hRH (by norm_num only : (1 : ℝ) ≤ 50000) le_rfl)
  linarith only [he.1]

/-- The real logarithm of 20/19 is at most 513/10000.
A six-term rational Taylor interval check proves this scalar input;
cast its upper endpoint to the real logarithm comparison. -/
theorem gamma_cutoff_ratio_log_upper : Real.log (20 / 19 : ℝ) ≤ 513 / 10000 := by
  have hc : Analysis.rationalLogIntervalCheck (20 / 19) 0 6 0 (513 / 10000) = true := by
    decide +kernel
  have h := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

/-- Under RH, the actual Chebyshev psi at 50000 is at least 47000.
Compare logarithmically weighted sums at 47500 and 50000, using the
certified errors and logarithm ratio upper bound. This avoids a finite
prime-power payload for the Chebyshev boundary input. -/
theorem gamma_psi_cutoff_lower (hRH : RiemannHypothesis) : (47000 : ℝ) ≤ Chebyshev.psi 50000 := by
  have hx :=
    gamma_smoothed_error_le_thirty_five hRH (by norm_num only : (1 : ℝ) ≤ 47500)
      (by norm_num only : (47500 : ℝ) ≤ 50000)
  have hy := gamma_smoothed_error_le_thirty_five hRH (by norm_num only : (1 : ℝ) ≤ 50000) le_rfl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.psi_bounds_of_logWeighted_error
        (by norm_num only : (0 : ℝ) < 47500) (by norm_num only : (47500 : ℝ) < 50000) hx hy).2
  have he : (50000 : ℝ) / 47500 = 20 / 19 := by norm_num only
  rw [he] at hp
  have hlog0 : 0 < Real.log (20 / 19 : ℝ) := Real.log_pos (by norm_num only)
  have hn : (47000 : ℝ) ≤ (50000 - 47500 - 35 - 35) / Real.log (20 / 19 : ℝ) := by
    apply (le_div_iff₀ hlog0).mpr
    linarith only [gamma_cutoff_ratio_log_upper]
  exact hn.trans hp

/-- Bounds for the finite prefix, positive Chebyshev boundary factors,
negative logarithmic slope, smoothed arithmetic value and tail main give
an upper bound for the actual finite center. Keep the signed products
and compare their factors using the stated nonnegativity conditions. -/
theorem gamma_center_le_of_interval_inputs {a U h p g A M : ℝ}
    (hU : (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.gammaResolventMangoldtWeight m) ≤ U)
    (hh : h ≤ Analysis.gammaResolventEulerWeight a) (hh0 : 0 ≤ h) (hp : p ≤ Chebyshev.psi a)
    (hp0 : 0 ≤ p) (hg : gammaEulerLogSlope a ≤ g) (hg0 : g ≤ 0)
    (hA : A ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a) (hA0 : 0 ≤ A)
    (hM : gammaEulerTailMain a ≤ M) : gammaEulerMassCenter a ≤ U - h * p + g * A + M := by
  have hhR := hh0.trans hh
  have hpR := hp0.trans hp
  have hprod := mul_le_mul hh hp hp0 hhR
  have hAreal := hA0.trans hA
  have hGprod := (mul_le_mul_of_nonneg_right hg hAreal).trans (mul_le_mul_of_nonpos_left hA hg0)
  dsimp only [gammaEulerMassCenter]
  linarith only [hU, hprod, hGprod, hM]

/-- Under RH, four explicit finite cutoff inputs suffice for total Euler
mass at most 25/2: prefix at most 59/10 and the displayed weight, slope
and tail-main bounds. The Chebyshev and smoothed lower bounds and the
infinite error allowance are already proved, so they are not extra inputs. -/
theorem gamma_mass_le_twelve_half_of_cutoff_inputs (hRH : RiemannHypothesis)
    (hU :
      (∑ m ∈ Finset.Ioc 0 ⌊(50000 : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight m) ≤ (59 / 10 : ℝ))
    (hh : (6716 / 1000000000 : ℝ) ≤ Analysis.gammaResolventEulerWeight 50000)
    (hg : gammaEulerLogSlope 50000 ≤ (-7106 / 1000000000 : ℝ))
    (hM : gammaEulerTailMain 50000 ≤ (7257 / 1000 : ℝ)) :
    (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) ≤ (25 / 2 : ℝ) := by
  have hc :=
    gamma_center_le_of_interval_inputs hU hh (by norm_num only : (0 : ℝ) ≤ 6716 / 1000000000)
      (gamma_psi_cutoff_lower hRH) (by norm_num only : (0 : ℝ) ≤ 47000) hg
      (by norm_num only : (-7106 / 1000000000 : ℝ) ≤ 0) (gamma_smoothed_cutoff_lower hRH)
      (by norm_num only : (0 : ℝ) ≤ 49965) hM
  have hm := (gammaEulerMass_bounds_50000 hRH).2
  linarith only [hc, hm]

end PseudoPrime.LLS
