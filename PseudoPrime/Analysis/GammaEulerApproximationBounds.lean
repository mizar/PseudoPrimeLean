/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaEulerApproximation
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-! # Uniform explicit error bounds for finite Euler Gamma products -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a real exponent and a natural order.
Output: n^sigma*n! divided by the product of sigma+j through j=n.
Role: express the real approximation with elementary factors. -/
noncomputable def gammaEulerRealApprox (σ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ σ * (n.factorial : ℝ) / ∏ j ∈ Finset.range (n + 1), (σ + (j : ℝ))

/-- Input: a positive real exponent and nonzero order.
Claim: the elementary real approximation is positive.
Proof: every denominator factor, the factorial and the real power are positive.
Role: permit logarithmic comparisons. -/
theorem gammaEulerRealApprox_pos {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : n ≠ 0) :
    0 < gammaEulerRealApprox σ n := by
  apply div_pos
  · exact
      mul_pos (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) σ)
        (Nat.cast_pos.mpr (Nat.factorial_pos n))
  · exact Finset.prod_pos (fun j _ ↦ add_pos_of_pos_of_nonneg hσ (Nat.cast_nonneg j))

/-- Input: a real exponent and any order.
Claim: the complex finite product at a real exponent is the embedding of its real formula.
Proof: commute casts with powers, products and division.
Role: identify the exact scalar approximation error. -/
theorem GammaSeq_ofReal_eq_realApprox (σ : ℝ) (n : ℕ) :
    Complex.GammaSeq (σ : ℂ) n = (gammaEulerRealApprox σ n : ℂ) := by
  rw [Complex.GammaSeq, gammaEulerRealApprox, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_prod]
  simp only [Complex.ofReal_add, Complex.ofReal_natCast]

/-- Input: a positive real exponent and nonzero order.
Claim: its logarithm equals the Bohr-Mollerup logarithmic approximation.
Proof: expand logarithms of positive powers and finite products.
Role: apply the existing quantitative log-convexity comparison. -/
theorem log_gammaEulerRealApprox {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : n ≠ 0) :
    Real.log (gammaEulerRealApprox σ n) = Real.BohrMollerup.logGammaSeq σ n := by
  have hp : 0 < ∏ j ∈ Finset.range (n + 1), (σ + (j : ℝ)) :=
    Finset.prod_pos (fun j _ ↦ add_pos_of_pos_of_nonneg hσ (Nat.cast_nonneg j))
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [gammaEulerRealApprox,
    Real.log_div (mul_pos (Real.rpow_pos_of_pos hn0 σ) (Nat.cast_pos.mpr (Nat.factorial_pos n))).ne'
      hp.ne',
    Real.log_mul (Real.rpow_pos_of_pos hn0 σ).ne' (Nat.cast_pos.mpr (Nat.factorial_pos n)).ne',
    Real.log_rpow hn0,
    Real.log_prod (fun j _ ↦ (add_pos_of_pos_of_nonneg hσ (Nat.cast_nonneg j)).ne')]
  rfl

/-- Input: a positive real argument.
Claim: log Gamma satisfies the additive Gamma recurrence.
Proof: take logarithms of the positive Gamma recurrence.
Role: instantiate the Bohr-Mollerup finite-order bound. -/
theorem logGamma_add_one_of_pos {y : ℝ} (hy : 0 < y) :
    (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
  dsimp only [Function.comp_apply]
  rw [Real.Gamma_add_one hy.ne', Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
  ring

/-- Input: a real exponent in (0,1] and nonzero order n.
Claim: the logarithmic approximation error is at most sigma/n.
Proof: use log convexity and log(1+1/n)<=1/n.
Role: turn convergence of Euler products into a uniform explicit rate. -/
theorem log_Gamma_sub_log_realApprox_le {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) {n : ℕ} (hn : n ≠ 0) :
    Real.log (Real.Gamma σ) - Real.log (gammaEulerRealApprox σ n) ≤ σ / n := by
  have h :=
    Real.BohrMollerup.le_logGammaSeq Real.convexOn_log_Gamma
      (fun {_} hy ↦ logGamma_add_one_of_pos hy) hσ hσ1 n
  dsimp only [Function.comp_apply] at h
  rw [Real.Gamma_one, Real.log_one, zero_add, ← log_gammaEulerRealApprox hσ hn] at h
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hlog := Real.log_le_sub_one_of_pos (div_pos (add_pos hn0 zero_lt_one) hn0)
  rw [Real.log_div (add_pos hn0 zero_lt_one).ne' hn0.ne'] at hlog
  have hdiv : ((n : ℝ) + 1) / n - 1 = 1 / n := by
    rw [add_div, div_self hn0.ne']
    ring
  rw [hdiv] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog hσ.le
  rw [← mul_div_assoc, mul_one, mul_sub] at hm
  linarith only [h, hm]

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: two positive real values.
Claim: their difference is at most the first value times the difference of logarithms.
Proof: apply log x <= x-1 to the ratio in the opposite order.
Role: convert logarithmic approximation bounds to absolute error bounds. -/
theorem sub_le_mul_log_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a - b ≤ a * (Real.log a - Real.log b) := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hb ha)) ha.le
  rw [Real.log_div hb.ne' ha.ne'] at h
  have he : a * (b / a - 1) = b - a := by
    calc
      _ = (b / a) * a - a := by ring
      _ = _ := by rw [div_mul_cancel₀ b ha.ne']
  rw [he] at h
  nlinarith only [h]

/-- Input: a real exponent in (0,1] and nonzero order.
Claim: the real Gamma approximation gap is at most sigma*Gamma(sigma)/n.
Proof: combine the logarithmic error with the logarithm difference inequality.
Role: supply a scalar certified rate for complex approximation. -/
theorem Gamma_sub_realApprox_le {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) {n : ℕ} (hn : n ≠ 0) :
    Real.Gamma σ - gammaEulerRealApprox σ n ≤ σ * Real.Gamma σ / n := by
  have hg := Real.Gamma_pos_of_pos hσ
  calc
    _ ≤ Real.Gamma σ * (Real.log (Real.Gamma σ) - Real.log (gammaEulerRealApprox σ n)) :=
      sub_le_mul_log_sub hg (gammaEulerRealApprox_pos hσ hn)
    _ ≤ Real.Gamma σ * (σ / n) :=
      mul_le_mul_of_nonneg_left (log_Gamma_sub_log_realApprox_le hσ hσ1 hn) hg.le
    _ = _ := by ring

/-- Input: a complex exponent with real part in (0,1] and nonzero order.
Claim: the complex approximation error is at most Re(s)*Gamma(Re(s))/n.
Proof: combine the positive integral error identity with the real quantitative gap.
Role: approximate Gamma phases with a finite elementary product. -/
theorem norm_Gamma_sub_GammaSeq_le {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1) {n : ℕ} (hn : n ≠ 0) :
    ‖Complex.Gamma s - Complex.GammaSeq s n‖ ≤ s.re * Real.Gamma s.re / n := by
  have h := norm_Gamma_sub_GammaSeq_le_real_gap hs hn
  rw [GammaSeq_ofReal_eq_realApprox, Complex.ofReal_re] at h
  exact h.trans (Gamma_sub_realApprox_le hs hs1 hn)

/-- Input: any real ordinate and nonzero order n.
Claim: the Gamma error on the half line is at most sqrt(pi)/(2*n), uniformly in the ordinate.
Proof: specialize the strip bound and use Gamma(1/2)=sqrt(pi).
Role: certify the low-frequency phase without an unproved Gamma numerical oracle. -/
theorem norm_Gamma_half_sub_GammaSeq_le (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) -
          Complex.GammaSeq ((1 / 2 : ℂ) + Complex.I * t) n‖ ≤
      Real.sqrt Real.pi / (2 * n) := by
  have hr : ((1 / 2 : ℂ) + Complex.I * t).re = (1 / 2 : ℝ) := by
    norm_num only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
      sub_zero, add_zero]
  have h :=
    norm_Gamma_sub_GammaSeq_le (s := (1 / 2 : ℂ) + Complex.I * t)
      (by
        rw [hr]; norm_num only)
      (by
        rw [hr]; norm_num only)
      hn
  rw [hr, Real.Gamma_one_half_eq] at h
  convert h using 1
  ring

end PseudoPrime.Analysis
