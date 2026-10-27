/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTrapezoidBounds
public import PseudoPrime.Analysis.GammaEulerApproximation

/-! # Positive corrected Euler density and its exact Gamma error mass -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a real argument below one. Claim: the quadratic logarithm defect has derivative
-t^2/(1-t). Proof: differentiate and clear the nonzero denominator.
Role: retain the quadratic term in Euler density comparisons. -/
theorem hasDerivAt_logQuadraticDefect {t : ℝ} (ht : t < 1) :
    HasDerivAt (fun x : ℝ ↦ Real.log (1 - x) + x + x ^ 2 / 2) (-(t ^ 2) / (1 - t)) t := by
  have hz : 1 - t ≠ 0 := (sub_pos.mpr ht).ne'
  have hd := (((hasDerivAt_id t).const_sub 1).log hz).add (hasDerivAt_id t)
  convert hd.add (((hasDerivAt_id t).pow 2).div_const 2) using 1
  · rfl
  · simp only [id_eq]
    field_simp (discharger := exact hz)
    ring

/-- Input: 0<=t<1. Claim: log(1-t)<=-t-t^2/2.
Proof: the defect has nonpositive derivative and vanishes at zero.
Role: prove that the corrected Euler density stays below the exponential. -/
theorem log_one_sub_le_quadratic {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    Real.log (1 - t) ≤ -t - t ^ 2 / 2 := by
  have hm :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iio (1 : ℝ))
      (fun u hu ↦ (hasDerivAt_logQuadraticDefect hu).continuousAt.continuousWithinAt)
      (fun u hu ↦
        (hasDerivAt_logQuadraticDefect (Set.mem_Iio.mp (interior_subset hu))).hasDerivWithinAt)
      (fun u hu ↦
        div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg u))
          (sub_nonneg.mpr (Set.mem_Iio.mp (interior_subset hu)).le))
  have h := hm (show (0 : ℝ) ∈ Set.Iio 1 by norm_num only [Set.mem_Iio]) ht1 ht
  simp only [sub_zero, Real.log_one, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero] at h
  linarith only [h]

/-- Input: a nonzero natural order and 0<=u<n.
Claim: (1-u/n)^n*(1+u^2/(2*n))<=exp(-u).
Proof: combine the quadratic log bound with log(1+v)<=v.
Role: preserve a nonnegative error after adding the quadratic density correction. -/
theorem corrected_euler_power_le_exp {n : ℕ} (hn : n ≠ 0) {u : ℝ} (hu : 0 ≤ u) (hun : u < n) :
    (1 - u / n) ^ n * (1 + u ^ 2 / (2 * n)) ≤ Real.exp (-u) := by
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hb : 0 < 1 - u / n := sub_pos.mpr ((div_lt_one hn0).mpr hun)
  have hv : 0 < 1 + u ^ 2 / (2 * n) :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (div_nonneg (sq_nonneg u) (mul_nonneg (by norm_num only) hn0.le))
  have hlog :=
    mul_le_mul_of_nonneg_left
      (log_one_sub_le_quadratic (div_nonneg hu hn0.le) ((div_lt_one hn0).mpr hun)) hn0.le
  have hlogv := Real.log_le_sub_one_of_pos hv
  apply (Real.log_le_iff_le_exp (mul_pos (pow_pos hb n) hv)).mp
  rw [Real.log_mul (pow_pos hb n).ne' hv.ne', Real.log_pow]
  have he : (n : ℝ) * (-(u / n) - (u / n) ^ 2 / 2) + u ^ 2 / (2 * n) = -u := by
    field_simp (discharger := exact hn0.ne')
    ring
  linarith only [hlog, hlogv, he]

/-- Input: a natural order and real integration variable.
Output: the truncated Euler density multiplied by 1+u^2/(2*n).
Role: cancel the first density error while preserving a positive approximation. -/
noncomputable def gammaEulerCorrectedCutoff (n : ℕ) (u : ℝ) : ℝ :=
  gammaEulerCutoff n u * (1 + u ^ 2 / (2 * n))

/-- Input: any order and real variable. Claim: the corrected density is nonnegative.
Proof: both factors are nonnegative. Role: support integral error estimates. -/
theorem gammaEulerCorrectedCutoff_nonneg (n : ℕ) (u : ℝ) : 0 ≤ gammaEulerCorrectedCutoff n u := by
  exact
    mul_nonneg (gammaEulerCutoff_nonneg n u)
      (add_nonneg zero_le_one
        (div_nonneg (sq_nonneg u) (mul_nonneg (by norm_num only) (Nat.cast_nonneg n))))

/-- Input: a nonzero order and any real variable.
Claim: the corrected density is bounded by exp(-u).
Proof: apply the interior power comparison and handle the cutoff endpoints separately.
Role: retain a nonnegative error density for complex Gamma approximation. -/
theorem gammaEulerCorrectedCutoff_le_exp {n : ℕ} (hn : n ≠ 0) (u : ℝ) :
    gammaEulerCorrectedCutoff n u ≤ Real.exp (-u) := by
  by_cases hm : u ∈ Set.Ioc (0 : ℝ) n
  · rw [gammaEulerCorrectedCutoff, gammaEulerCutoff, Set.indicator_of_mem hm]
    rcases hm.2.eq_or_lt with he | hl
    · rw [he, div_self (Nat.cast_ne_zero.mpr hn), sub_self, zero_pow hn, zero_mul]
      exact (Real.exp_pos _).le
    · exact corrected_euler_power_le_exp hn hm.1.le hl
  · rw [gammaEulerCorrectedCutoff, gammaEulerCutoff, Set.indicator_of_notMem hm, zero_mul]
    exact (Real.exp_pos _).le

/-- Input: a complex exponent and natural order.
Output: GammaSeq(s,n)+GammaSeq(s+2,n)/(2*n).
Role: represent the corrected density integral by finite elementary products. -/
noncomputable def gammaEulerCorrectedApprox (s : ℂ) (n : ℕ) : ℂ :=
  Complex.GammaSeq s n + (2 * (n : ℂ))⁻¹ * Complex.GammaSeq (s + 2) n

/-- Input: an order, complex exponent and positive integration variable.
Claim: the corrected integrand splits into the original and shifted-power terms.
Proof: use the addition law for positive-base complex powers.
Role: transfer the correction to finite Euler products. -/
theorem gammaEulerCorrected_integrand (n : ℕ) (s : ℂ) {u : ℝ} (hu : 0 < u) :
    (gammaEulerCorrectedCutoff n u : ℂ) * (u : ℂ) ^ (s - 1) =
      (gammaEulerCutoff n u : ℂ) * (u : ℂ) ^ (s - 1) +
        (2 * (n : ℂ))⁻¹ * ((gammaEulerCutoff n u : ℂ) * (u : ℂ) ^ ((s + 2) - 1)) := by
  have he : s + 2 - 1 = (s - 1) + 2 := by ring
  rw [he, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne'), Complex.cpow_ofNat,
    gammaEulerCorrectedCutoff, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_natCast]
  ring

/-- Input: an order and exponent with positive real part.
Claim: the corrected complex density is integrable on the positive halfline.
Proof: split into the known Euler integrands at s and s+2.
Role: justify evaluation and subtraction of the corrected integral. -/
theorem integrable_gammaEulerCorrected_cpow (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ (gammaEulerCorrectedCutoff n u : ℂ) * (u : ℂ) ^ (s - 1))
      (Set.Ioi 0) := by
  have hs2 : 0 < (s + 2).re := by
    change 0 < s.re + 2
    linarith only [hs]
  have hi :=
    (integrable_gammaEulerCutoff_cpow n hs).add
      ((integrable_gammaEulerCutoff_cpow n hs2).const_mul (2 * (n : ℂ))⁻¹)
  exact hi.congr_fun (fun u hu ↦ (gammaEulerCorrected_integrand n s hu).symm) measurableSet_Ioi

/-- Input: a nonzero order and exponent with positive real part.
Claim: the corrected integral equals gammaEulerCorrectedApprox.
Proof: split the integral and apply both beta-integral evaluations.
Role: replace the special function by corrected finite products. -/
theorem integral_gammaEulerCorrected_eq {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    (∫ u : ℝ in Set.Ioi 0, (gammaEulerCorrectedCutoff n u : ℂ) * (u : ℂ) ^ (s - 1)) =
      gammaEulerCorrectedApprox s n := by
  have hs2 : 0 < (s + 2).re := by
    change 0 < s.re + 2
    linarith only [hs]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun u hu ↦ gammaEulerCorrected_integrand n s hu),
    MeasureTheory.integral_add (integrable_gammaEulerCutoff_cpow n hs)
      ((integrable_gammaEulerCutoff_cpow n hs2).const_mul (2 * (n : ℂ))⁻¹),
    MeasureTheory.integral_const_mul, integral_gammaEulerCutoff_eq_GammaSeq hs hn,
    integral_gammaEulerCutoff_eq_GammaSeq hs2 hn]
  rfl

/-- Input: an order, real exponent and nonnegative integration variable.
Claim: the real part of the embedded integrand is the real-power density.
Proof: commute complex embeddings with real powers and products.
Role: identify the scalar error mass. -/
theorem gammaEulerCorrected_real_part (n : ℕ) (σ : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    ((gammaEulerCorrectedCutoff n u : ℂ) * (u : ℂ) ^ ((σ : ℂ) - 1)).re =
      gammaEulerCorrectedCutoff n u * u ^ (σ - 1) := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow hu, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- Input: an order and positive real exponent.
Claim: the real corrected density is integrable on the positive halfline.
Proof: take real parts of the complex integral.
Role: permit scalar error integration. -/
theorem integrable_gammaEulerCorrected_real (n : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ gammaEulerCorrectedCutoff n u * u ^ (σ - 1))
      (Set.Ioi 0) := by
  have hi := integrable_gammaEulerCorrected_cpow n (show 0 < (σ : ℂ).re from hσ)
  exact hi.re.congr_fun (fun u hu ↦ gammaEulerCorrected_real_part n σ hu.le) measurableSet_Ioi

/-- Input: a nonzero order and positive real exponent.
Claim: the scalar integral equals the real part of the corrected finite product.
Proof: commute real parts with integration and use the complex evaluation.
Role: compute the exact mass controlling every imaginary ordinate. -/
theorem integral_gammaEulerCorrected_real_eq {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : n ≠ 0) :
    (∫ u : ℝ in Set.Ioi 0, gammaEulerCorrectedCutoff n u * u ^ (σ - 1)) =
      (gammaEulerCorrectedApprox (σ : ℂ) n).re := by
  have hi := integrable_gammaEulerCorrected_cpow n (show 0 < (σ : ℂ).re from hσ)
  calc
    _ = ∫ u : ℝ in Set.Ioi 0, ((gammaEulerCorrectedCutoff n u : ℂ) * (u : ℂ) ^ ((σ : ℂ) - 1)).re :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun u hu ↦ (gammaEulerCorrected_real_part n σ hu.le).symm)
    _ = (∫ u : ℝ in Set.Ioi 0, (gammaEulerCorrectedCutoff n u : ℂ) * (u : ℂ) ^ ((σ : ℂ) - 1)).re :=
      Complex.reCLM.integral_comp_comm hi
    _ = _ := congrArg Complex.re (integral_gammaEulerCorrected_eq (show 0 < (σ : ℂ).re from hσ) hn)

/-- Input: a nonzero order, exponent and positive integration variable.
Claim: the complex error integrand norm equals its nonnegative scalar density.
Proof: factor the error and evaluate the norm of a positive-base complex power.
Role: obtain a height-independent corrected approximation bound. -/
theorem gammaEulerCorrected_error_norm {n : ℕ} (hn : n ≠ 0) (s : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖(Real.exp (-u) : ℂ) * (u : ℂ) ^ (s - 1) -
          (gammaEulerCorrectedCutoff n u : ℂ) * (u : ℂ) ^ (s - 1)‖ =
      (Real.exp (-u) - gammaEulerCorrectedCutoff n u) * u ^ (s.re - 1) := by
  rw [← sub_mul, ← Complex.ofReal_sub, norm_mul,
    Complex.norm_of_nonneg (sub_nonneg.mpr (gammaEulerCorrectedCutoff_le_exp hn u)),
    Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.sub_re, Complex.one_re]

/-- Input: a nonzero order and complex exponent with positive real part.
Claim: the Gamma error is bounded by the real corrected approximation gap.
Proof: preserve the positive error density under the integral norm.
Role: certify phases with a directly evaluable scalar error mass. -/
theorem norm_Gamma_sub_corrected_le_real_gap {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    ‖Complex.Gamma s - gammaEulerCorrectedApprox s n‖ ≤
      Real.Gamma s.re - (gammaEulerCorrectedApprox (s.re : ℂ) n).re := by
  have hg := Complex.GammaIntegral_convergent hs
  have ha := integrable_gammaEulerCorrected_cpow n hs
  have hr := (Real.GammaIntegral_convergent hs).sub (integrable_gammaEulerCorrected_real n hs)
  rw [Complex.Gamma_eq_integral hs, ← integral_gammaEulerCorrected_eq hs hn]
  dsimp only [Complex.GammaIntegral]
  rw [← MeasureTheory.integral_sub hg ha]
  calc
    _ ≤ ∫ u : ℝ in Set.Ioi 0, (Real.exp (-u) - gammaEulerCorrectedCutoff n u) * u ^ (s.re - 1) := by
      apply
        MeasureTheory.norm_integral_le_of_norm_le
          (hr.congr_fun
            (fun u _ ↦ by
              dsimp only [Pi.sub_apply]; ring)
            measurableSet_Ioi)
      exact
        MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
          (fun u hu ↦ (gammaEulerCorrected_error_norm hn s hu).le)
    _ = _ := by
      simp_rw [sub_mul]
      rw [MeasureTheory.integral_sub (Real.GammaIntegral_convergent hs)
          (integrable_gammaEulerCorrected_real n hs),
        ← Real.Gamma_eq_integral hs, integral_gammaEulerCorrected_real_eq hs hn]

/-- Input: a nonzero order and positive real exponent.
Claim: the corrected real approximation is at least the original one.
Proof: integrate the nonnegative added density.
Role: show that the exact corrected error allowance improves the original allowance. -/
theorem gammaEulerCorrectedApprox_improves_real {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : n ≠ 0) :
    (Complex.GammaSeq (σ : ℂ) n).re ≤ (gammaEulerCorrectedApprox (σ : ℂ) n).re := by
  have h :=
    MeasureTheory.setIntegral_mono_on (integrable_gammaEulerCutoff_real n hσ)
      (integrable_gammaEulerCorrected_real n hσ) measurableSet_Ioi (fun u hu ↦ ?_)
  · rw [integral_gammaEulerCutoff_real_eq_GammaSeq hσ hn,
      integral_gammaEulerCorrected_real_eq hσ hn] at h
    exact h
  · apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hu.le (σ - 1))
    dsimp only [gammaEulerCorrectedCutoff]
    have hp :=
      mul_nonneg (gammaEulerCutoff_nonneg n u)
        (div_nonneg (sq_nonneg u) (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (Nat.cast_nonneg n)))
    nlinarith only [hp]

/-- Input: a nonzero order and exponents s and s+1 different from zero.
Claim: the corrected approximation is one Euler product times a rational multiplier.
Proof: apply the finite Gamma recurrence twice and cancel the nonzero order.
Role: evaluate the corrected phase without duplicating a long product. -/
theorem gammaEulerCorrectedApprox_factor {s : ℂ} (hs : s ≠ 0) (hs1 : s + 1 ≠ 0) {n : ℕ}
    (hn : n ≠ 0) :
    gammaEulerCorrectedApprox s n =
      Complex.GammaSeq s n *
        (1 + s * (s + 1) * (n : ℂ) / (2 * ((n : ℂ) + 1 + s) * ((n : ℂ) + 1 + (s + 1)))) := by
  have h1 := (div_eq_iff hs).mp (Complex.GammaSeq_add_one_left s hn)
  have h2 := (div_eq_iff hs1).mp (Complex.GammaSeq_add_one_left (s + 1) hn)
  have he : s + 2 = (s + 1) + 1 := by ring
  rw [gammaEulerCorrectedApprox, he, h2, h1]
  have hnz : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp (discharger :=
    first
    | exact hnz
    | norm_num only)

end PseudoPrime.Analysis
