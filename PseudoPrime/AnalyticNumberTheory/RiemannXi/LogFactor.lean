/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.Basic
public import PseudoPrime.AnalyticNumberTheory.Gamma.EulerLogSeries

/-! # Exponential factorization of xi -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- The logarithm of the non-zeta factor in the xi factorization. Its two
principal logarithms and the Euler-normalized Gamma logarithm supply a
continuous phase on paths avoiding their branch cuts. -/
noncomputable def xiLogFactor (s : ℂ) : ℂ :=
  Complex.log s + Complex.log (s - 1) - (s / 2) * (Real.log Real.pi : ℂ) +
    Gamma.logGammaSeries (s / 2)

/-- The xi logarithmic factor is differentiable at any point with positive
real part where `s - 1` lies in the logarithm's slit plane. Each principal
logarithm and the normalized Gamma logarithm is differentiable there. -/
theorem differentiableAt_xiLogFactor {s : ℂ} (hs : 0 < s.re) (hcut : s - 1 ∈ Complex.slitPlane) :
    DifferentiableAt ℂ xiLogFactor s := by
  have h0 : s ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hs)
  have h2 : 0 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    exact div_pos hs (by norm_num only)
  have hg := (Gamma.hasDerivAt_logGammaSeries h2).differentiableAt
  have hd : DifferentiableAt ℂ (fun z : ℂ ↦ z / 2) s := differentiableAt_id.div_const 2
  unfold xiLogFactor
  exact
    ((((Complex.differentiableAt_log h0).comp s differentiableAt_id).add
              ((Complex.differentiableAt_log hcut).comp s (differentiableAt_id.sub_const 1))).sub
          (hd.mul_const _)).add
      (hg.comp s hd)

/-- For positive real part and `s ≠ 1`, xi is one half the exponential of
its logarithmic factor times zeta. Gamma's recurrence and the normalized
Gamma logarithm turn the existing xi factorization into this form. -/
theorem riemannXi_eq_exp_factor {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s = (1 / 2 : ℂ) * Complex.exp (xiLogFactor s) * riemannZeta s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hs2 : s / 2 ≠ 0 := div_ne_zero hs0 (by norm_num only)
  have hs2r : 0 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    exact div_pos hs (by norm_num only)
  have hs21 : 0 < (s / 2 + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith only [hs2r]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hd : (2 : ℂ) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num only) (Complex.cpow_ne_zero_iff.mpr (Or.inl hp)))
      (Complex.Gamma_ne_zero (Gamma.not_neg_nat_of_re_pos hs21))
  rw [riemannXi_eq_mul_riemannZeta_of_denom_ne_zero hs1 hd]
  rw [Complex.Gamma_add_one (s / 2) hs2, Gamma.Gamma_eq_exp_logGammaSeries hs2r]
  rw [Complex.cpow_def_of_ne_zero hp, ← Complex.ofReal_log Real.pi_pos.le]
  unfold xiLogFactor
  rw [Complex.exp_add, Complex.exp_sub, Complex.exp_add, Complex.exp_log hs0,
    Complex.exp_log (sub_ne_zero.mpr hs1)]
  have he :
    Complex.exp (-(s / 2 * (Real.log Real.pi : ℂ))) =
      (Complex.exp ((Real.log Real.pi : ℂ) * (-s / 2))) := by
    congr 1
    ring
  rw [← he, Complex.exp_neg, div_eq_mul_inv]
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannXi
