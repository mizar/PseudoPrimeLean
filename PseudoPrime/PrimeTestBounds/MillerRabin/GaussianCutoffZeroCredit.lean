/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogWeightedExact
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSmoothedInterpolation
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedLogSplit
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.FiniteZeroSums
import PseudoPrime.LLS.RiemannWeightedErrorBounds

/-! # Signed low-zero credit for Gaussian cutoff estimates -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem log_zero_norm_mass (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    (∑' ρ : ℂ, ‖AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm x ρ‖) ≤
      Real.sqrt x / 20 := by
  let m (ρ : ℂ) : ℝ :=
    if AnalyticNumberTheory.RiemannXi.riemannXi ρ = 0 then
      (AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity ρ : ℝ) / Complex.normSq ρ
    else 0
  have hs := (AnalyticNumberTheory.RiemannZeta.summable_nontrivialLogZeroTerm hx).norm
  have hm : Summable m := AnalyticNumberTheory.RiemannXi.summable_zeroMultiplicityInvNormSq_RH hRH
  have h :=
    hs.tsum_le_tsum (g := fun ρ ↦ Real.sqrt x * m ρ)
      (fun ρ ↦ by
        by_cases hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re
        · have hxi := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz.1 hz.2
          simp only [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, hz, and_self,
            ↓reduceIte, m, hxi,
            AnalyticNumberTheory.RiemannXi.zeroMultiplicity_eq_zetaMultiplicity_of_zero hxi]
          rw [AnalyticNumberTheory.RiemannZeta.norm_riemannZetaLogZeroContribution_of_rh hRH
              (zero_lt_one.trans_le hx) hz.1 hz.2,
            mul_div_assoc]
        · simp only [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, hz, ↓reduceIte,
            norm_zero]
          apply mul_nonneg (Real.sqrt_nonneg _)
          unfold m
          split
          · exact div_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
          · exact le_rfl)
      (hm.mul_left _)
  rw [tsum_mul_left] at h
  have hmass := AnalyticNumberTheory.RiemannXi.tsum_multiplicityInvSq_eq_two_mass_RH hRH
  change (∑' ρ, m ρ) = _ at hmass
  rw [hmass] at h
  linarith only [h,
    mul_le_mul_of_nonneg_left AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth
      (Real.sqrt_nonneg x)]

/-- Under RH any finite set of zero terms improves the absolute estimate
by the sum of their real parts plus their norms. All omitted credits are
nonnegative, so one can use just the ordinates with favorable phases. -/
theorem gaussian_log_zero_credit (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) (S : Finset ℂ) :
    let z := AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm x
    (∑ ρ ∈ S, ((z ρ).re + ‖z ρ‖)) - Real.sqrt x / 20 ≤ (∑' ρ, z ρ).re := by
  intro z
  have hs : Summable z := AnalyticNumberTheory.RiemannZeta.summable_nontrivialLogZeroTerm hx
  have hr := Complex.reCLM.summable hs
  have hm := hs.norm
  have h :=
    (hr.add hm).sum_le_tsum S
      (fun ρ _ ↦ by
        change 0 ≤ (z ρ).re + ‖z ρ‖
        linarith only [(abs_le.mp (Complex.abs_re_le_norm (z ρ))).1])
  rw [hr.tsum_add hm, ← Complex.reCLM.map_tsum hs] at h
  have hmass := log_zero_norm_mass hRH hx
  simp only [Complex.reCLM_apply] at h
  change (∑' ρ, ‖z ρ‖) ≤ Real.sqrt x / 20 at hmass
  linarith only [h, hmass]

private theorem log_pole_trivial_bound (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re +
        AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries x ≤
      21 / 20 := by
  have he := AnalyticNumberTheory.RiemannZeta.log_weighted_exact_one
  rw [LLS.logWeightedMangoldtSum_eq_zero_of_le_one le_rfl, Real.log_one, mul_zero] at he
  have hZ := log_zero_norm_mass hRH (le_refl (1 : ℝ))
  have hz :=
    (Complex.abs_re_le_norm _).trans
      (norm_tsum_le_tsum_norm
        (AnalyticNumberTheory.RiemannZeta.summable_nontrivialLogZeroTerm (le_refl (1 : ℝ))).norm)
  have hZ' : (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm 1 ρ).re ≤ 1 / 20 :=
    (le_abs_self _).trans (hz.trans (by simpa only [Real.sqrt_one] using hZ))
  have ht :
    AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries 1 = Real.pi ^ 2 / 24 := by
    unfold AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries
    simp only [inv_one, one_pow]
    have h :
      (fun k : ℕ ↦ (1 : ℝ) / (4 * ((k : ℝ) + 1) ^ 2)) = fun k : ℕ ↦
        (1 / 4 : ℝ) * (1 / ((k : ℝ) + 1) ^ 2) := by
      funext k
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      field_simp [hk.ne']
    rw [h, tsum_mul_left, Analysis.tsum_shifted_basel_eq]
    ring
  linarith only [he, hZ', ht, AnalyticNumberTheory.RiemannZeta.logTrivialSeries_le_pi_sq_div_24 hx]

/-- The exact smoothed error retains the credit of any selected zero terms.
The pole and the trivial zeros together cost at most 21/20. -/
theorem gaussian_log_error_of_credit (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) (S : Finset ℂ) :
    let z := AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm x
    (∑ ρ ∈ S, ((z ρ).re + ‖z ρ‖)) - Real.sqrt x / 20 - 21 / 20 ≤ gaussianLogError (Real.log x) := by
  intro z
  have hz := gaussian_log_zero_credit hRH hx.le S
  dsimp only at hz
  unfold gaussianLogError
  rw [Real.exp_log (zero_lt_one.trans hx), AnalyticNumberTheory.RiemannZeta.log_weighted_exact hx]
  dsimp only [z]
  linarith only [hz, log_pole_trivial_bound hRH hx]

/-- On the radius range of the first compressed cell, a selected-zero
credit of 8.65 is enough for the signed Abel cutoff requirement. -/
theorem gaussian_first_cutoff_of_credit (hRH : RiemannHypothesis) {y : ℝ}
    (hy : y ∈ Set.Icc (663 / 2 : ℝ) 332) (S : Finset ℂ)
    (hS :
      let z := AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm (y ^ 2)
      8.65 ≤ ∑ ρ ∈ S, ((z ρ).re + ‖z ρ‖)) :
    -9 ≤ gaussianLogError (Real.log (y ^ 2)) := by
  have hy₀ : 1 < y := by linarith only [hy.1]
  have hz := gaussian_log_error_of_credit hRH (one_lt_pow₀ hy₀ (by decide : 2 ≠ 0)) S
  dsimp only at hz hS
  rw [Real.sqrt_sq (zero_le_one.trans hy₀.le)] at hz
  linarith only [hz, hS, hy.2]

end PseudoPrime.PrimeTestBounds.MillerRabin
