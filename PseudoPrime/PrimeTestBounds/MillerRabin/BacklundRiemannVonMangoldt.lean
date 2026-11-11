/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeEleventhsThetaInputs
import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundXiVerticalPhase
import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundXiHorizontalPhase
import PseudoPrime.AnalyticNumberTheory.RiemannXi.UpperRectangleIntegrable

/-! # Euler-normalized Riemann–von Mangoldt identity under RH -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem central_log_arguments {t : ℝ} (ht : 0 < t) :
    (Complex.log (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im +
        (Complex.log ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)).im =
      Real.pi := by
  let w : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hw : w.im = t := by
    simp only [w, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  have hn : ((starRingEnd ℂ) w).im < 0 := by
    rw [Complex.conj_im, hw]
    exact neg_neg_of_pos ht
  have hpi : w.arg ≠ Real.pi := by
    intro h
    have hzero := (Complex.arg_eq_pi_iff.mp h).2
    rw [hw] at hzero
    exact ht.ne' hzero
  have he : w - 1 = -(starRingEnd ℂ) w := by
    apply Complex.ext
    · simp only [w, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.one_re,
        Complex.neg_re, Complex.conj_re]
      norm_num only
    · simp only [w, Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add,
        Complex.one_im, sub_zero, Complex.neg_im, Complex.conj_im, neg_neg]
  change (Complex.log w).im + (Complex.log (w - 1)).im = Real.pi
  rw [Complex.log_im, Complex.log_im, he, Complex.arg_neg_eq_arg_add_pi_of_im_neg hn,
    Complex.arg_conj, ite_eq_right hpi]
  ring

private theorem central_factor_phase {t : ℝ} (ht : 0 < t) :
    (AnalyticNumberTheory.RiemannXi.xiLogFactor (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im =
      Real.pi + backlundTheta t := by
  have hlogs := central_log_arguments ht
  let w : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hdiv : w / 2 = ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
    dsimp only [w]
    push_cast
    ring
  change (Complex.log w).im + (Complex.log (w - 1)).im = Real.pi at hlogs
  unfold AnalyticNumberTheory.RiemannXi.xiLogFactor backlundTheta
  change
    (Complex.log w + Complex.log (w - 1) - (w / 2) * (Real.log Real.pi : ℂ) +
          AnalyticNumberTheory.Gamma.logGammaSeries (w / 2)).im =
      _
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    hdiv, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
  linarith only [hlogs]

private theorem count_eq_central_phase (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 < t)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) (φ : ℝ → ℝ)
    (hc : ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)))
    (hp :
      ∀ x : ℝ,
        x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
          riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I) =
            (‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) *
              Complex.exp ((φ x : ℂ) * Complex.I))
    (hn :
      φ (3 / 2) =
        (AnalyticNumberTheory.RiemannZeta.backlundZetaLog
            (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im) :
    Real.pi * AnalyticNumberTheory.RiemannZeta.positiveZeroCount t =
      (AnalyticNumberTheory.RiemannXi.xiLogFactor (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im +
        φ (1 / 2) := by
  have h := AnalyticNumberTheory.RiemannXi.positiveZeroCount_edge_integrals hRH ht hgood
  rw [xi_vertical_arg_integral, xi_upper_arg_integral ht hgood φ hc hp] at h
  simp only [xiVerticalLog, Complex.add_im] at h
  linarith only [h, hn]

/-- Under RH, the Euler-normalized Riemann–von Mangoldt identity holds at
every required good height for every argument with the prescribed Euler
anchor. The finite rectangle count and the two edge arguments give the
central phase, whose two elementary logarithms contribute exactly `π`. -/
theorem euler_riemann_von_mangoldt_of_RH (hRH : RiemannHypothesis) : EulerRiemannVonMangoldt := by
  intro t ht hgood φ hc hp hn
  have hbase : 0 < 2 * Real.pi * Real.exp 1 :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)
  have ht0 : 0 < t := hbase.trans_le ht
  have h := count_eq_central_phase hRH ht0 hgood φ hc hp hn
  rw [central_factor_phase ht0] at h
  have hdiv := congrArg (fun x : ℝ ↦ x / Real.pi) h
  rw [mul_div_cancel_left₀ _ Real.pi_ne_zero, add_div, add_div, div_self Real.pi_ne_zero] at hdiv
  exact hdiv

end PseudoPrime.PrimeTestBounds.MillerRabin
