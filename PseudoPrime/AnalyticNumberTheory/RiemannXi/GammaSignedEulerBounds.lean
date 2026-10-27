/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CenteredHadamard
public import PseudoPrime.Analysis.GammaResolventGridCertificate
public import PseudoPrime.Analysis.ListInfiniteSum
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaSignedEulerIdentity
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.LogDerivGammaFactor

/-! # Signed Gamma resolvent mass from the real xi Poisson identity -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- Input: a point on the critical line and a natural multiplicity.
Claim: subtracting half the genus term at one leaves the real Poisson kernel.
Proof: expand real inverses and cancel equal endpoint norm squares.
Role: cancel reciprocal-zero terms without estimating their absolute values. -/
theorem real_genus_centering (σ : ℝ) (ρ : ℂ) (k : ℕ) (hr : ρ.re = 1 / 2) :
    ((k : ℂ) * (1 / ((σ : ℂ) - ρ) + 1 / ρ)).re -
        (1 / 2 : ℝ) * ((k : ℂ) * (1 / (1 - ρ) + 1 / ρ)).re =
      (k : ℝ) * ((σ - 1 / 2) / ((σ - 1 / 2) ^ 2 + ρ.im ^ 2)) := by
  have h0 : Complex.normSq ρ = 1 / 4 + ρ.im ^ 2 := by
    rw [Complex.normSq_apply, hr]
    ring
  have h1 : Complex.normSq (1 - ρ) = 1 / 4 + ρ.im ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      hr]
    ring
  have hs : Complex.normSq ((σ : ℂ) - ρ) = (σ - 1 / 2) ^ 2 + ρ.im ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, hr]
    ring
  simp only [one_div, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.add_re,
    Complex.inv_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re, hr, zero_mul, sub_zero, h0,
    h1, hs]
  ring

/-- Input: RH, a real argument and an arbitrary complex point.
Claim: the centered genus difference equals the multiplicity-weighted Poisson term.
Proof: use the critical line at zeros; elsewhere the analytic order is zero.
Role: extend the term identity to the all-point convergent series. -/
theorem real_genus_centering_all (hRH : RiemannHypothesis) (σ : ℝ) (ρ : ℂ) :
    ((analyticOrderNatAt riemannXi ρ : ℂ) * (1 / ((σ : ℂ) - ρ) + 1 / ρ)).re -
        (1 / 2 : ℝ) * ((analyticOrderNatAt riemannXi ρ : ℂ) * (1 / (1 - ρ) + 1 / ρ)).re =
      (analyticOrderNatAt riemannXi ρ : ℝ) * ((σ - 1 / 2) / ((σ - 1 / 2) ^ 2 + ρ.im ^ 2)) := by
  by_cases hz : riemannXi ρ = 0
  · exact real_genus_centering σ ρ _ (riemannXi_zero_re_eq_half_of_riemannHypothesis hRH hz)
  · have ho : analyticOrderNatAt riemannXi ρ = 0 := by
      rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hz), ENat.toNat_zero]
    simp only [ho, Nat.cast_zero, zero_mul, Complex.zero_re, mul_zero, sub_zero]

/-- Input: RH and a real argument strictly above one half.
Claim: the real Poisson zero series sums to the real xi logarithmic derivative.
Proof: subtract half the expansion at one and use the xi functional equation.
Role: preserve positivity in finite signed resolvent combinations. -/
theorem hasSum_real_poisson (hRH : RiemannHypothesis) {σ : ℝ} (hσ : 1 / 2 < σ) :
    HasSum
      (fun ρ : ℂ ↦
        (analyticOrderNatAt riemannXi ρ : ℝ) * ((σ - 1 / 2) / ((σ - 1 / 2) ^ 2 + ρ.im ^ 2)))
      (logDeriv riemannXi (σ : ℂ)).re := by
  have hs : (1 / 2 : ℝ) < (σ : ℂ).re := hσ
  have h1 : (1 / 2 : ℝ) < (1 : ℂ).re := by norm_num only [Complex.one_re]
  have hS := Complex.hasSum_re (summable_genus_terms_of_riemannHypothesis hRH hs).hasSum
  have hO := Complex.hasSum_re (summable_genus_terms_of_riemannHypothesis hRH h1).hasSum
  rw [← centered_logDeriv_eq_genusSum_of_riemannHypothesis hRH hs] at hS
  rw [← centered_logDeriv_eq_genusSum_of_riemannHypothesis hRH h1] at hO
  have hh := hS.sub (hO.mul_left (1 / 2 : ℝ))
  have he :
    (logDeriv riemannXi (σ : ℂ) - logDeriv riemannXi 0).re -
        (1 / 2 : ℝ) * (logDeriv riemannXi 1 - logDeriv riemannXi 0).re =
      (logDeriv riemannXi (σ : ℂ)).re := by
    rw [logDeriv_riemannXi_one_eq_neg_zero]
    simp only [Complex.sub_re, Complex.neg_re]
    ring
  rw [he] at hh
  simpa only [real_genus_centering_all hRH] using hh

/-- Input: RH.
Claim: the signed xi derivative combination is exactly the Gamma resolvent zero mass.
Proof: interchange the finite signed list and convergent Poisson series.
Role: retain coefficient cancellation before applying positivity. -/
theorem gammaResolvent_zeroMass_eq_real_logDeriv (hRH : RiemannHypothesis) :
    (∑' ρ : ℂ, (analyticOrderNatAt riemannXi ρ : ℝ) * Analysis.gammaResolventMajorant ρ.im) =
      (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) * (logDeriv riemannXi (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum := by
  have hn (ab : ℚ × ℚ) (hab : ab ∈ Analysis.gammaResolventCoefficients) :
    HasSum
      (fun ρ : ℂ ↦
        (analyticOrderNatAt riemannXi ρ : ℝ) * ((ab.1 : ℝ) / ((ab.1 : ℝ) ^ 2 + ρ.im ^ 2)))
      (logDeriv riemannXi (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re := by
    have ha :=
      Rat.cast_lt (K := ℝ) |>.mpr
        (List.forall_iff_forall_mem.mp Analysis.gammaResolvent_scales_gt_half ab hab)
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at ha
    have hh := hasSum_real_poisson hRH (show (1 / 2 : ℝ) < 1 / 2 + (ab.1 : ℝ) by linarith only [ha])
    simpa only [add_sub_cancel_left, Complex.ofReal_add] using hh
  have he (ρ : ℂ) :
    (analyticOrderNatAt riemannXi ρ : ℝ) * Analysis.gammaResolventMajorant ρ.im =
      (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              ((analyticOrderNatAt riemannXi ρ : ℝ) *
                ((ab.1 : ℝ) / ((ab.1 : ℝ) ^ 2 + ρ.im ^ 2))))).sum := by
    rw [Analysis.gammaResolventMajorant, ← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro ab _
    ring
  rw [tsum_congr he,
    Analysis.tsum_list_sum Analysis.gammaResolventCoefficients _
      (fun ab hab ↦ (hn ab hab).summable.mul_left (ab.2 : ℝ))]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  rw [tsum_mul_left, (hn ab hab).tsum_eq]

/-- Input: RH.
Claim: the signed xi derivative combination is nonnegative.
Proof: identify its zero mass and use the certified nonnegative Gamma majorant.
Role: bound the common Euler mass without a finite prime prefix certificate. -/
theorem gammaResolvent_real_logDeriv_nonneg (hRH : RiemannHypothesis) :
    0 ≤
      (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) * (logDeriv riemannXi (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum := by
  rw [← gammaResolvent_zeroMass_eq_real_logDeriv hRH]
  exact
    tsum_nonneg
      (fun ρ ↦
        mul_nonneg (Nat.cast_nonneg _)
          ((norm_nonneg _).trans (Analysis.norm_Gamma_half_add_I_le_gammaResolvent ρ.im)))

/-- Input: the fixed certified resolvent coefficients.
Claim: the signed real zeta derivative combination is minus the common Euler mass.
Proof: specialize the exact character Euler identity to modulus one.
Role: connect xi positivity to the nonnegative prime-power sum. -/
theorem gammaResolvent_signed_zeta_eq_neg_euler :
    (Analysis.gammaResolventCoefficients.map
          (fun ab ↦ (ab.2 : ℝ) * (logDeriv riemannZeta (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum =
      -(∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) := by
  have h := DirichletLFunction.gammaResolvent_signed_ordinary_eq_euler (1 : DirichletCharacter ℂ 1)
  have hc (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) 1, map_one]
  simpa only [DirichletCharacter.LFunction_modOne_eq, hc, Complex.one_re, neg_one_mul,
    tsum_neg] using h

/-- Input: RH.
Claim: the common Euler mass is bounded by the signed pole and Gamma contributions.
Proof: separate xi into poles, Gamma and zeta, retaining coefficient signs.
Role: replace absolute-node Euler allowances by a principal-character bound. -/
theorem gammaResolvent_euler_le_poles_gamma (hRH : RiemannHypothesis) :
    (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) ≤
      (Analysis.gammaResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (1 / ((1 / 2 : ℝ) + (ab.1 : ℝ)) + 1 / ((ab.1 : ℝ) - 1 / 2)))).sum +
        (Analysis.gammaResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) *
                (logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor
                    (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum := by
  have he :
    (Analysis.gammaResolventCoefficients.map
          (fun ab ↦ (ab.2 : ℝ) * (logDeriv riemannXi (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum =
      (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              ((1 / ((1 / 2 : ℝ) + (ab.1 : ℝ)) + 1 / ((ab.1 : ℝ) - 1 / 2)) +
                (logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor
                    (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re +
                (logDeriv riemannZeta (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re))).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro ab hab
    have ha :=
      Rat.cast_lt (K := ℝ) |>.mpr
        (List.forall_iff_forall_mem.mp Analysis.gammaResolvent_scales_gt_half ab hab)
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at ha
    have hs : 1 < ((((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith only [ha]
    have hpole (t : ℝ) : (1 / (t : ℂ)).re = 1 / t := by
      rw [one_div, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
    rw [logDeriv_eq_poles_gammaFactor_zeta_of_one_lt_re hs]
    simp only [Complex.add_re, ← Complex.ofReal_add, ← Complex.ofReal_one, ← Complex.ofReal_sub]
    have hd : (1 / 2 : ℝ) + (ab.1 : ℝ) - 1 = (ab.1 : ℝ) - 1 / 2 := by ring
    rw [hd]
    simp only [Complex.ofReal_one, hpole]
  simp only [mul_add, List.sum_map_add] at he
  rw [gammaResolvent_signed_zeta_eq_neg_euler] at he
  have hp := gammaResolvent_real_logDeriv_nonneg hRH
  simp only [mul_add, List.sum_map_add]
  linarith only [he, hp]

/-- Input: the fixed rational nodes.
Claim: the signed elementary pole sum is strictly below fourteen.
Proof: exact rational arithmetic.
Role: give a short scalar bound with no input enumeration. -/
theorem gammaResolvent_pole_sum_lt_fourteen :
    (Analysis.gammaResolventCoefficients.map
          (fun ab ↦ (ab.2 : ℝ) * (1 / ((1 / 2 : ℝ) + (ab.1 : ℝ)) + 1 / ((ab.1 : ℝ) - 1 / 2)))).sum <
      14 := by
  norm_num only [Analysis.gammaResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]

/-- Input: RH.
Claim: the common Euler mass is below fourteen plus the signed Gamma contribution.
Proof: combine the exact analytic comparison with the rational pole bound.
Role: isolate the remaining signed archimedean numerical estimate. -/
theorem gammaResolvent_euler_lt_fourteen_add_gamma (hRH : RiemannHypothesis) :
    (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) <
      14 +
        (Analysis.gammaResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) *
                (logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor
                    (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum := by
  have he := gammaResolvent_euler_le_poles_gamma hRH
  have hp := gammaResolvent_pole_sum_lt_fourteen
  linarith only [he, hp]

end PseudoPrime.AnalyticNumberTheory.RiemannXi
