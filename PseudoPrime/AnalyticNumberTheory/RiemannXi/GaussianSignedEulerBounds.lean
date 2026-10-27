/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.GammaSignedEulerBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GaussianSignedEulerIdentity

/-! # Gaussian Euler mass bounded through the signed xi identity -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- Input: RH.
Claim: the signed xi derivative combination is exactly the Gaussian resolvent zero mass.
Proof: interchange the finite signed list and convergent Poisson series.
Role: retain coefficient cancellation before applying positivity. -/
theorem gaussianResolvent_zeroMass_eq_real_logDeriv (hRH : RiemannHypothesis) :
    (∑' ρ : ℂ, (analyticOrderNatAt riemannXi ρ : ℝ) * Analysis.gaussianResolventMajorant ρ.im) =
      (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) * (logDeriv riemannXi (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum := by
  have hn (ab : ℚ × ℚ) (hab : ab ∈ Analysis.gaussianResolventCoefficients) :
    HasSum
      (fun ρ : ℂ ↦
        (analyticOrderNatAt riemannXi ρ : ℝ) * ((ab.1 : ℝ) / ((ab.1 : ℝ) ^ 2 + ρ.im ^ 2)))
      (logDeriv riemannXi (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re := by
    have ha :=
      Rat.cast_lt (K := ℝ) |>.mpr
        (List.forall_iff_forall_mem.mp Analysis.gaussianResolvent_scales_gt_half ab hab)
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at ha
    have hh := hasSum_real_poisson hRH (show (1 / 2 : ℝ) < 1 / 2 + (ab.1 : ℝ) by linarith only [ha])
    simpa only [add_sub_cancel_left, Complex.ofReal_add] using hh
  have he (ρ : ℂ) :
    (analyticOrderNatAt riemannXi ρ : ℝ) * Analysis.gaussianResolventMajorant ρ.im =
      (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) *
              ((analyticOrderNatAt riemannXi ρ : ℝ) *
                ((ab.1 : ℝ) / ((ab.1 : ℝ) ^ 2 + ρ.im ^ 2))))).sum := by
    rw [Analysis.gaussianResolventMajorant, ← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro ab _
    ring
  rw [tsum_congr he,
    Analysis.tsum_list_sum Analysis.gaussianResolventCoefficients _
      (fun ab hab ↦ (hn ab hab).summable.mul_left (ab.2 : ℝ))]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  rw [tsum_mul_left, (hn ab hab).tsum_eq]

/-- Input: RH.
Claim: the signed xi derivative combination is nonnegative.
Proof: identify its zero mass and use the certified nonnegative Gaussian majorant.
Role: bound the common Euler mass without a finite prime prefix certificate. -/
theorem gaussianResolvent_real_logDeriv_nonneg (hRH : RiemannHypothesis) :
    0 ≤
      (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) * (logDeriv riemannXi (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum := by
  rw [← gaussianResolvent_zeroMass_eq_real_logDeriv hRH]
  exact
    tsum_nonneg
      (fun ρ ↦
        mul_nonneg (Nat.cast_nonneg _)
          ((norm_nonneg _).trans
            (Analysis.norm_gaussianGammaFunction_le_gaussianResolvent_of_grid
              Analysis.gaussianResolvent_grid_lower ρ.im)))

/-- Input: the fixed certified resolvent coefficients.
Claim: the signed real zeta derivative combination is minus the common Euler mass.
Proof: specialize the exact character Euler identity to modulus one.
Role: connect xi positivity to the nonnegative prime-power sum. -/
theorem gaussianResolvent_signed_zeta_eq_neg_euler :
    (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦ (ab.2 : ℝ) * (logDeriv riemannZeta (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum =
      -(∑' n : ℕ, Analysis.gaussianResolventMangoldtWeight n) := by
  have h :=
    DirichletLFunction.gaussianResolvent_signed_ordinary_eq_euler (1 : DirichletCharacter ℂ 1)
  have hc (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) 1, map_one]
  simpa only [DirichletCharacter.LFunction_modOne_eq, hc, Complex.one_re, neg_one_mul,
    tsum_neg] using h

/-- Input: RH.
Claim: the common Euler mass is bounded by the signed pole and Gamma contributions.
Proof: separate xi into poles, Gamma and zeta, retaining coefficient signs.
Role: replace absolute-node Euler allowances by a principal-character bound. -/
theorem gaussianResolvent_euler_le_poles_gamma (hRH : RiemannHypothesis) :
    (∑' n : ℕ, Analysis.gaussianResolventMangoldtWeight n) ≤
      (Analysis.gaussianResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (1 / ((1 / 2 : ℝ) + (ab.1 : ℝ)) + 1 / ((ab.1 : ℝ) - 1 / 2)))).sum +
        (Analysis.gaussianResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) *
                (logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor
                    (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum := by
  have he :
    (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦ (ab.2 : ℝ) * (logDeriv riemannXi (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum =
      (Analysis.gaussianResolventCoefficients.map
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
        (List.forall_iff_forall_mem.mp Analysis.gaussianResolvent_scales_gt_half ab hab)
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
  rw [gaussianResolvent_signed_zeta_eq_neg_euler] at he
  have hp := gaussianResolvent_real_logDeriv_nonneg hRH
  simp only [mul_add, List.sum_map_add]
  linarith only [he, hp]

/-- Input: the fixed rational nodes.
Claim: the signed elementary pole sum is strictly below fifteen_tenth.
Proof: exact rational arithmetic.
Role: give a short scalar bound with no input enumeration. -/
theorem gaussianResolvent_pole_sum_lt_fifteen_tenth :
    (Analysis.gaussianResolventCoefficients.map
          (fun ab ↦ (ab.2 : ℝ) * (1 / ((1 / 2 : ℝ) + (ab.1 : ℝ)) + 1 / ((ab.1 : ℝ) - 1 / 2)))).sum <
      151 / 10 := by
  norm_num only [Analysis.gaussianResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]

/-- Input: RH.
Claim: the common Euler mass is below fifteen_tenth plus the signed Gamma contribution.
Proof: combine the exact analytic comparison with the rational pole bound.
Role: isolate the remaining signed archimedean numerical estimate. -/
theorem gaussianResolvent_euler_lt_fifteen_tenth_add_gamma (hRH : RiemannHypothesis) :
    (∑' n : ℕ, Analysis.gaussianResolventMangoldtWeight n) <
      151 / 10 +
        (Analysis.gaussianResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) *
                (logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor
                    (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum := by
  have he := gaussianResolvent_euler_le_poles_gamma hRH
  have hp := gaussianResolvent_pole_sum_lt_fifteen_tenth
  linarith only [he, hp]

end PseudoPrime.AnalyticNumberTheory.RiemannXi
