/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Positive integral error for finite Euler Gamma products -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a natural approximation order and a real integration variable.
Output: (1-u/n)^n on the interval (0,n], and zero outside it.
Role: approximate the Gamma exponential density from below. -/
noncomputable def gammaEulerCutoff (n : ℕ) (u : ℝ) : ℝ :=
  (Set.Ioc (0 : ℝ) n).indicator (fun v ↦ (1 - v / n) ^ n) u

/-- Input: any order and real argument. Claim: the truncated Euler density is nonnegative.
Proof: the active interval makes the base nonnegative; outside it the density vanishes.
Role: preserve positivity in the error integral. -/
theorem gammaEulerCutoff_nonneg (n : ℕ) (u : ℝ) : 0 ≤ gammaEulerCutoff n u := by
  by_cases hm : u ∈ Set.Ioc (0 : ℝ) n
  · rw [gammaEulerCutoff, Set.indicator_of_mem hm]
    exact pow_nonneg (sub_nonneg.mpr (div_le_one_of_le₀ hm.2 (Nat.cast_nonneg n))) n
  · rw [gammaEulerCutoff, Set.indicator_of_notMem hm]

/-- Input: any order and real argument. Claim: the truncated Euler density is at most exp(-u).
Proof: use the exponential power inequality on the active interval.
Role: make the Gamma approximation error a nonnegative density. -/
theorem gammaEulerCutoff_le_exp (n : ℕ) (u : ℝ) : gammaEulerCutoff n u ≤ Real.exp (-u) := by
  by_cases hm : u ∈ Set.Ioc (0 : ℝ) n
  · rw [gammaEulerCutoff, Set.indicator_of_mem hm]
    exact Real.one_sub_div_pow_le_exp_neg hm.2
  · rw [gammaEulerCutoff, Set.indicator_of_notMem hm]
    exact (Real.exp_pos (-u)).le

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: an order, a complex exponent and a real argument.
Claim: the cut-off complex integrand equals the corresponding interval indicator.
Proof: split membership in the cut-off interval.
Role: identify finite Euler integrals without adding a convergence assumption. -/
theorem gammaEulerCutoff_mul_cpow_eq_indicator (n : ℕ) (s : ℂ) (u : ℝ) :
    (gammaEulerCutoff n u : ℂ) * (u : ℂ) ^ (s - 1) =
      (Set.Ioc (0 : ℝ) n).indicator (fun v ↦ (((1 - v / n) ^ n : ℝ) : ℂ) * (v : ℂ) ^ (s - 1))
        u := by
  by_cases hm : u ∈ Set.Ioc (0 : ℝ) n
  · rw [gammaEulerCutoff, Set.indicator_of_mem hm, Set.indicator_of_mem hm]
  · rw [gammaEulerCutoff, Set.indicator_of_notMem hm, Set.indicator_of_notMem hm,
      Complex.ofReal_zero, zero_mul]

/-- Input: any order and a complex exponent with positive real part.
Claim: the cut-off Gamma integrand is integrable on the positive halfline.
Proof: use interval integrability of complex powers and a continuous polynomial multiplier.
Role: justify subtraction and real-part passage in the error identity. -/
theorem integrable_gammaEulerCutoff_cpow (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ (gammaEulerCutoff n u : ℂ) * (u : ℂ) ^ (s - 1))
      (Set.Ioi 0) := by
  have hp : -1 < (s - 1).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith only [hs]
  have hi :=
    (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := (n : ℝ)) hp).continuousOn_mul
      (Complex.continuous_ofReal.comp
          (((continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ))).sub
                (continuous_id.div_const (n : ℝ))).pow
            n)).continuousOn
  simp_rw [gammaEulerCutoff_mul_cpow_eq_indicator]
  rw [MeasureTheory.IntegrableOn, MeasureTheory.integrable_indicator_iff measurableSet_Ioc,
    MeasureTheory.IntegrableOn,
    MeasureTheory.Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).mp hi

/-- Input: an order, a real exponent and a nonnegative base.
Claim: the complex integrand's real part equals the real power integrand.
Proof: positive real powers commute with the complex embedding.
Role: identify the scalar mass controlling the complex error. -/
theorem gammaEulerCutoff_real_part (n : ℕ) (σ : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    ((gammaEulerCutoff n u : ℂ) * (u : ℂ) ^ ((σ : ℂ) - 1)).re =
      gammaEulerCutoff n u * u ^ (σ - 1) := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow hu, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- Input: any order and a positive real exponent.
Claim: the real cut-off Gamma integrand is integrable on the positive halfline.
Proof: take real parts of the integrable complex integrand.
Role: justify the exact real approximation gap. -/
theorem integrable_gammaEulerCutoff_real (n : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ gammaEulerCutoff n u * u ^ (σ - 1)) (Set.Ioi 0) := by
  have hi := integrable_gammaEulerCutoff_cpow n (show 0 < (σ : ℂ).re from hσ)
  exact hi.re.congr_fun (fun u hu ↦ gammaEulerCutoff_real_part n σ hu.le) measurableSet_Ioi

/-- Input: a complex exponent with positive real part and a nonzero natural order.
Claim: the cut-off halfline integral equals the finite Euler product GammaSeq.
Proof: restrict the indicator integral and apply the beta-integral evaluation.
Role: replace the special function by a finite product with an explicit error. -/
theorem integral_gammaEulerCutoff_eq_GammaSeq {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    (∫ u : ℝ in Set.Ioi 0, (gammaEulerCutoff n u : ℂ) * (u : ℂ) ^ (s - 1)) =
      Complex.GammaSeq s n := by
  simp_rw [gammaEulerCutoff_mul_cpow_eq_indicator]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    MeasureTheory.Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self, ←
    intervalIntegral.integral_of_le (Nat.cast_nonneg n),
    Complex.GammaSeq_eq_approx_Gamma_integral hs hn]

/-- Input: a positive real exponent and nonzero order.
Claim: the scalar cut-off integral equals the real part of the real-argument finite product.
Proof: commute real parts with the integrable complex integral.
Role: measure the total mass of the nonnegative approximation error. -/
theorem integral_gammaEulerCutoff_real_eq_GammaSeq {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : n ≠ 0) :
    (∫ u : ℝ in Set.Ioi 0, gammaEulerCutoff n u * u ^ (σ - 1)) =
      (Complex.GammaSeq (σ : ℂ) n).re := by
  have hi := integrable_gammaEulerCutoff_cpow n (show 0 < (σ : ℂ).re from hσ)
  calc
    _ = ∫ u : ℝ in Set.Ioi 0, ((gammaEulerCutoff n u : ℂ) * (u : ℂ) ^ ((σ : ℂ) - 1)).re := by
      exact
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          (fun u hu ↦ (gammaEulerCutoff_real_part n σ hu.le).symm)
    _ = (∫ u : ℝ in Set.Ioi 0, (gammaEulerCutoff n u : ℂ) * (u : ℂ) ^ ((σ : ℂ) - 1)).re :=
      Complex.reCLM.integral_comp_comm hi
    _ = _ :=
      congrArg Complex.re (integral_gammaEulerCutoff_eq_GammaSeq (show 0 < (σ : ℂ).re from hσ) hn)

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: a natural order and a positive real exponent.
Claim: the scalar nonnegative Gamma error density is integrable.
Proof: subtract the two known integrable densities.
Role: dominate the complex approximation error. -/
theorem gammaEuler_error_integrable (n : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ (Real.exp (-u) - gammaEulerCutoff n u) * u ^ (σ - 1))
      (Set.Ioi 0) := by
  have hi := (Real.GammaIntegral_convergent hσ).sub (integrable_gammaEulerCutoff_real n hσ)
  exact
    hi.congr_fun
      (fun u _ ↦ by
        dsimp only [Pi.sub_apply]; ring)
      measurableSet_Ioi

/-- Input: any order, complex exponent and positive integration variable.
Claim: the complex integrand difference has norm exactly the scalar error density.
Proof: factor the nonnegative density and evaluate the norm of a positive-base complex power.
Role: obtain a height-independent approximation bound. -/
theorem gammaEuler_error_norm (n : ℕ) (s : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖(Real.exp (-u) : ℂ) * (u : ℂ) ^ (s - 1) - (gammaEulerCutoff n u : ℂ) * (u : ℂ) ^ (s - 1)‖ =
      (Real.exp (-u) - gammaEulerCutoff n u) * u ^ (s.re - 1) := by
  rw [← sub_mul, ← Complex.ofReal_sub, norm_mul,
    Complex.norm_of_nonneg (sub_nonneg.mpr (gammaEulerCutoff_le_exp n u)),
    Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.sub_re, Complex.one_re]

/-- Input: a complex exponent with positive real part and a nonzero order.
Claim: the complex Gamma error is at most the real Gamma approximation gap at its real part.
Proof: retain the positive density difference under the norm of the integral.
Role: reduce complex phase certification to a scalar real error bound. -/
theorem norm_Gamma_sub_GammaSeq_le_real_gap {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    ‖Complex.Gamma s - Complex.GammaSeq s n‖ ≤
      Real.Gamma s.re - (Complex.GammaSeq (s.re : ℂ) n).re := by
  have hg := Complex.GammaIntegral_convergent hs
  have ha := integrable_gammaEulerCutoff_cpow n hs
  have hr := gammaEuler_error_integrable n hs
  rw [Complex.Gamma_eq_integral hs, ← integral_gammaEulerCutoff_eq_GammaSeq hs hn]
  dsimp only [Complex.GammaIntegral]
  rw [← MeasureTheory.integral_sub hg ha]
  calc
    _ ≤ ∫ u : ℝ in Set.Ioi 0, (Real.exp (-u) - gammaEulerCutoff n u) * u ^ (s.re - 1) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hr
      exact
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
          (fun u hu ↦ (gammaEuler_error_norm n s hu).le)
    _ = _ := by
      simp_rw [sub_mul]
      rw [MeasureTheory.integral_sub (Real.GammaIntegral_convergent hs)
          (integrable_gammaEulerCutoff_real n hs),
        ← Real.Gamma_eq_integral hs, integral_gammaEulerCutoff_real_eq_GammaSeq hs hn]

end PseudoPrime.Analysis
