/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Trigamma at one half and one

Differentiating the logarithmic derivative of Euler's Gamma reflection identity once
at `1/2` gives `digamma'(1/2) = π²/2`. Differentiating the corresponding duplication
identity once then gives `digamma'(1) = π²/6`. Analyticity away from Gamma's poles
justifies these local differentiations. The resulting special values enter the
second-logarithmic-derivative comparison between xi and zeta.
-/

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- Every point within `r ≤ c` of a positive real `c` avoids every nonpositive integer. -/
theorem ball_avoids_nonpos_int {c r : ℝ} (hr : 0 < r) (hrc : r ≤ c) :
    ∀ w ∈ Metric.ball (c : ℂ) r, ∀ m : ℕ, w ≠ -m := by
  intro w hw m hcontra
  rw [Metric.mem_ball, hcontra] at hw
  have heq : (-(m : ℂ) - (c : ℂ)) = ((-(m : ℝ) - c : ℝ) : ℂ) := by
    push_cast; ring
  rw [dist_eq_norm, heq, Complex.norm_real, Real.norm_eq_abs] at hw
  have hle : (-(m : ℝ) - c) ≤ 0 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  rw [abs_of_nonpos hle] at hw
  linarith [Nat.cast_nonneg (α := ℝ) m]

/-- `Γ` is analytic at the center of any ball avoiding every nonpositive integer. -/
theorem analyticAt_Gamma_of_ball {s : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ w ∈ Metric.ball s r, ∀ m : ℕ, w ≠ -m) : AnalyticAt ℂ Complex.Gamma s := by
  apply DifferentiableOn.analyticAt (s := Metric.ball s r)
  · intro w hw
    exact (Complex.differentiableAt_Gamma w (hball w hw)).differentiableWithinAt
  · exact Metric.ball_mem_nhds s hr

theorem analyticAt_Gamma_half : AnalyticAt ℂ Complex.Gamma (1 / 2 : ℂ) :=
  analyticAt_Gamma_of_ball (r := 1 / 4) (by norm_num only)
    (by
      simpa only [one_div, Metric.mem_ball, ne_eq, Complex.ofReal_inv, Complex.ofReal_ofNat] using
        ball_avoids_nonpos_int (c := 1 / 2) (r := 1 / 4) (by norm_num only) (by norm_num only))

theorem analyticAt_Gamma_one : AnalyticAt ℂ Complex.Gamma (1 : ℂ) :=
  analyticAt_Gamma_of_ball (r := 1 / 2) (by norm_num only)
    (by
      simpa only [one_div, Metric.mem_ball, ne_eq, Complex.ofReal_one] using
        ball_avoids_nonpos_int (c := 1) (r := 1 / 2) (by norm_num only) (by norm_num only))

/-- `digamma` is analytic (hence differentiable) wherever `Γ` is analytic and nonzero. -/
theorem analyticAt_digamma {s : ℂ} (hs : AnalyticAt ℂ Complex.Gamma s) (hne : Complex.Gamma s ≠ 0) :
    AnalyticAt ℂ Complex.digamma s := by
  rw [Complex.digamma_def]
  unfold logDeriv
  exact hs.deriv.div hs hne

theorem half_ne_neg_nat (m : ℕ) : (1 / 2 : ℂ) ≠ -m := by
  intro h
  have hm : (1 / 2 : ℝ) = -(m : ℝ) := by
    have h' : ((1 / 2 : ℝ) : ℂ) = (-(m : ℝ) : ℂ) := by
      convert h using 1
      norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast,
        Complex.ofReal_ofNat, Nat.cast_ofNat]
    exact_mod_cast h'
  nlinarith only [hm, Nat.cast_nonneg (α := ℝ) m]

theorem one_ne_neg_nat (m : ℕ) : (1 : ℂ) ≠ -m := by
  intro h
  have hm : (1 : ℝ) = -(m : ℝ) := by
    have h' : ((1 : ℝ) : ℂ) = (-(m : ℝ) : ℂ) := by convert h using 1
    exact_mod_cast h'
  nlinarith only [Nat.cast_nonneg (α := ℝ) m, hm]

theorem differentiableAt_digamma_half : DifferentiableAt ℂ Complex.digamma (1 / 2 : ℂ) :=
  (analyticAt_digamma analyticAt_Gamma_half
      (Complex.Gamma_ne_zero half_ne_neg_nat)).differentiableAt

theorem differentiableAt_digamma_one : DifferentiableAt ℂ Complex.digamma (1 : ℂ) :=
  (analyticAt_digamma analyticAt_Gamma_one (Complex.Gamma_ne_zero one_ne_neg_nat)).differentiableAt

theorem ball_half_avoids_int : ∀ w ∈ Metric.ball (1 / 2 : ℂ) (1 / 4), ∀ k : ℤ, w ≠ k := by
  intro w hw k hcontra
  rw [Metric.mem_ball, hcontra] at hw
  have heq : ((k : ℂ) - 1 / 2) = (((k : ℝ) - 1 / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [dist_eq_norm, heq, Complex.norm_real, Real.norm_eq_abs] at hw
  have hbound : (1 : ℝ) / 2 ≤ |(k : ℝ) - 1 / 2| := by
    by_cases hk : k ≤ 0
    · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk
      rw [abs_of_nonpos (by linarith)]; linarith
    · have hk1 : 1 ≤ k := by omega
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      rw [abs_of_nonneg (by linarith)]; linarith
  linarith

theorem sin_pi_mul_ne_zero_of_ball {z : ℂ} (hz : z ∈ Metric.ball (1 / 2 : ℂ) (1 / 4)) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  intro hcontra
  rw [Complex.sin_eq_zero_iff] at hcontra
  obtain ⟨k, hk⟩ := hcontra
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hzk : z = (k : ℂ) :=
    mul_left_cancel₀ hpi
      (by
        rw [hk]; ring)
  exact ball_half_avoids_int z hz k hzk

theorem one_sub_mem_ball_half {z : ℂ} (hz : z ∈ Metric.ball (1 / 2 : ℂ) (1 / 4)) :
    (1 - z) ∈ Metric.ball (1 / 2 : ℂ) (1 / 4) := by
  rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
  have heq : (1 - z - 1 / 2 : ℂ) = -(z - 1 / 2) := by ring
  rw [heq, norm_neg]
  exact hz

/-- **Reflection formula, differentiated once**: `digamma z - digamma (1-z) = -π cot(πz)`, on the
ball where both `z` and `1-z` avoid nonpositive integers. Obtained by differentiating both
`Γ z * Γ (1-z)` (product rule, via `Γ' = Γ * digamma`) and its equal `π / sin(πz)`
(`Complex.Gamma_mul_Gamma_one_sub`), then matching the two derivative values
(`HasDerivAt.unique`) and cancelling the shared nonzero factor `Γ z * Γ (1-z)`. -/
theorem digamma_sub_digamma_one_sub_eq {z : ℂ} (hz : z ∈ Metric.ball (1 / 2 : ℂ) (1 / 4)) :
    Complex.digamma z - Complex.digamma (1 - z) =
      -(Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z) / Complex.sin ((Real.pi : ℂ) * z) := by
  have hcast : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast,
      Complex.ofReal_ofNat, Nat.cast_ofNat]
  have hz1 : ∀ m : ℕ, z ≠ -m := by
    have h := ball_avoids_nonpos_int (c := 1 / 2) (r := 1 / 4) (by norm_num only) (by norm_num only)
    rw [hcast] at h
    exact h z hz
  have hz2 : ∀ m : ℕ, (1 - z) ≠ -m := by
    have h := ball_avoids_nonpos_int (c := 1 / 2) (r := 1 / 4) (by norm_num only) (by norm_num only)
    rw [hcast] at h
    exact h (1 - z) (one_sub_mem_ball_half hz)
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := sin_pi_mul_ne_zero_of_ball hz
  have hGz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hz1
  have hG1z : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero hz2
  have hd1 : HasDerivAt Complex.Gamma (Complex.Gamma z * Complex.digamma z) z := by
    have hdiff := Complex.differentiableAt_Gamma z hz1
    have heq : Complex.Gamma z * Complex.digamma z = deriv Complex.Gamma z := by
      rw [Complex.digamma_def, logDeriv_apply]; field_simp [hGz]
    rw [heq]; exact hdiff.hasDerivAt
  have hd2 :
    HasDerivAt Complex.Gamma (Complex.Gamma (1 - z) * Complex.digamma (1 - z)) (1 - z) := by
    have hdiff := Complex.differentiableAt_Gamma (1 - z) hz2
    have heq : Complex.Gamma (1 - z) * Complex.digamma (1 - z) = deriv Complex.Gamma (1 - z) := by
      rw [Complex.digamma_def, logDeriv_apply]; field_simp [hG1z]
    rw [heq]; exact hdiff.hasDerivAt
  have hd2' :
    HasDerivAt (fun w : ℂ => Complex.Gamma (1 - w))
      (-(Complex.Gamma (1 - z) * Complex.digamma (1 - z))) z :=
    hd2.comp_const_sub 1 z
  have hprod :
    HasDerivAt (fun w : ℂ => Complex.Gamma w * Complex.Gamma (1 - w))
      (Complex.Gamma z * Complex.digamma z * Complex.Gamma (1 - z) +
        Complex.Gamma z * (-(Complex.Gamma (1 - z) * Complex.digamma (1 - z))))
      z :=
    hd1.mul hd2'
  have hprod' :
    HasDerivAt (fun w : ℂ => (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w))
      (Complex.Gamma z * Complex.digamma z * Complex.Gamma (1 - z) +
        Complex.Gamma z * (-(Complex.Gamma (1 - z) * Complex.digamma (1 - z))))
      z := by
    have hcongr :
      (fun w : ℂ => Complex.Gamma w * Complex.Gamma (1 - w)) =
        (fun w : ℂ => (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w)) :=
      funext Complex.Gamma_mul_Gamma_one_sub
    rwa [hcongr] at hprod
  have hsinD :
    HasDerivAt (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w))
      (Complex.cos ((Real.pi : ℂ) * z) * (Real.pi : ℂ)) z := by
    have h1 : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) (Real.pi : ℂ) z := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id z).const_mul (Real.pi : ℂ)
    exact (Complex.hasDerivAt_sin ((Real.pi : ℂ) * z)).comp z h1
  have hquot :
    HasDerivAt (fun w : ℂ => (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w))
      ((0 * Complex.sin ((Real.pi : ℂ) * z) -
          (Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * z) * (Real.pi : ℂ))) /
        (Complex.sin ((Real.pi : ℂ) * z)) ^ 2)
      z :=
    (hasDerivAt_const z (Real.pi : ℂ)).div hsinD hsin
  have hEq := hprod'.unique hquot
  have hGprod :
    Complex.Gamma z * Complex.Gamma (1 - z) = (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z) :=
    Complex.Gamma_mul_Gamma_one_sub z
  have hfactor :
    Complex.Gamma z * Complex.digamma z * Complex.Gamma (1 - z) +
        Complex.Gamma z * (-(Complex.Gamma (1 - z) * Complex.digamma (1 - z))) =
      Complex.Gamma z * Complex.Gamma (1 - z) * (Complex.digamma z - Complex.digamma (1 - z)) := by
    ring
  rw [hfactor] at hEq
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hGnezero : Complex.Gamma z * Complex.Gamma (1 - z) ≠ 0 := by
    rw [hGprod]; exact div_ne_zero hpiC hsin
  have key :
    Complex.Gamma z * Complex.Gamma (1 - z) * (Complex.digamma z - Complex.digamma (1 - z)) =
      Complex.Gamma z * Complex.Gamma (1 - z) *
        (-(Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z) / Complex.sin ((Real.pi : ℂ) * z)) := by
    rw [hEq, hGprod]
    field_simp
    ring
  exact mul_left_cancel₀ hGnezero key

/-- The derivative of `-π cot(πz)` at `z = 1/2` is `π ^ 2` (`sin(π/2) = 1`, `cos(π/2) = 0` kill the
cross terms in the quotient rule). -/
theorem hasDerivAt_reflection_rhs_half :
    HasDerivAt
      (fun z : ℂ =>
        -(Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z) / Complex.sin ((Real.pi : ℂ) * z))
      ((Real.pi : ℂ) ^ 2) (1 / 2 : ℂ) := by
  have hsin_half : Complex.sin ((Real.pi : ℂ) * (1 / 2 : ℂ)) ≠ 0 := by
    have hcast : (Real.pi : ℂ) * (1 / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, ← Complex.ofReal_sin]
    have hval : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    rw [hval]
    norm_num only [Complex.ofReal_one]
  have hcosD :
    HasDerivAt (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w))
      (-Complex.sin ((Real.pi : ℂ) * (1 / 2 : ℂ)) * (Real.pi : ℂ)) (1 / 2 : ℂ) := by
    have h1 : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) (Real.pi : ℂ) (1 / 2 : ℂ) := by
      simpa only [one_div, id_eq, mul_one] using (hasDerivAt_id (1 / 2 : ℂ)).const_mul (Real.pi : ℂ)
    exact (Complex.hasDerivAt_cos ((Real.pi : ℂ) * (1 / 2 : ℂ))).comp (1 / 2 : ℂ) h1
  have hsinD :
    HasDerivAt (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w))
      (Complex.cos ((Real.pi : ℂ) * (1 / 2 : ℂ)) * (Real.pi : ℂ)) (1 / 2 : ℂ) := by
    have h1 : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) (Real.pi : ℂ) (1 / 2 : ℂ) := by
      simpa only [one_div, id_eq, mul_one] using (hasDerivAt_id (1 / 2 : ℂ)).const_mul (Real.pi : ℂ)
    exact (Complex.hasDerivAt_sin ((Real.pi : ℂ) * (1 / 2 : ℂ))).comp (1 / 2 : ℂ) h1
  have hquot :
    HasDerivAt (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w) / Complex.sin ((Real.pi : ℂ) * w))
      ((-Complex.sin ((Real.pi : ℂ) * (1 / 2 : ℂ)) * (Real.pi : ℂ) *
            Complex.sin ((Real.pi : ℂ) * (1 / 2 : ℂ)) -
          Complex.cos ((Real.pi : ℂ) * (1 / 2 : ℂ)) *
            (Complex.cos ((Real.pi : ℂ) * (1 / 2 : ℂ)) * (Real.pi : ℂ))) /
        (Complex.sin ((Real.pi : ℂ) * (1 / 2 : ℂ))) ^ 2)
      (1 / 2 : ℂ) :=
    hcosD.div hsinD hsin_half
  have hval :
    Complex.sin ((Real.pi : ℂ) * (1 / 2 : ℂ)) = 1 ∧
      Complex.cos ((Real.pi : ℂ) * (1 / 2 : ℂ)) = 0 := by
    have heq : (Real.pi : ℂ) * (1 / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [heq, ← Complex.ofReal_sin, ← Complex.ofReal_cos, Real.sin_pi_div_two, Real.cos_pi_div_two]
    constructor <;> trivial
  have hquot' :
    HasDerivAt (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w) / Complex.sin ((Real.pi : ℂ) * w))
      (-(Real.pi : ℂ)) (1 / 2 : ℂ) := by
    convert hquot using 1
    simp only [hval.1, hval.2]
    ring
  have hfinal := hquot'.const_mul (-(Real.pi : ℂ))
  have heq :
    (fun y : ℂ =>
        -(Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * y) / Complex.sin ((Real.pi : ℂ) * y))) =
      (fun z : ℂ =>
        -(Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z) / Complex.sin ((Real.pi : ℂ) * z)) := by
    funext y; rw [mul_div_assoc]
  rw [heq] at hfinal
  have hval2 : -(Real.pi : ℂ) * -(Real.pi : ℂ) = (Real.pi : ℂ) ^ 2 := by ring
  rw [hval2] at hfinal
  exact hfinal

/-- `digamma'(1/2) = π²/2`, obtained by differentiating the digamma reflection
identity once near `1/2` and using the chain rule at `1-1/2 = 1/2`. -/
theorem deriv_digamma_half_eq : deriv Complex.digamma (1 / 2 : ℂ) = (Real.pi : ℂ) ^ 2 / 2 := by
  have heventually :
    (fun z : ℂ => Complex.digamma z - Complex.digamma (1 - z)) =ᶠ[nhds (1 / 2 : ℂ)]
      (fun z : ℂ =>
        -(Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z) / Complex.sin ((Real.pi : ℂ) * z)) := by
    filter_upwards [Metric.ball_mem_nhds (1 / 2 : ℂ) (by norm_num only : (0 : ℝ) < 1 / 4)] with z hz
    exact digamma_sub_digamma_one_sub_eq hz
  have hderiv_eq := heventually.deriv_eq
  rw [hasDerivAt_reflection_rhs_half.deriv] at hderiv_eq
  have hsplit :
    deriv (fun z : ℂ => Complex.digamma z - Complex.digamma (1 - z)) (1 / 2 : ℂ) =
      deriv Complex.digamma (1 / 2 : ℂ) -
        deriv (fun z : ℂ => Complex.digamma (1 - z)) (1 / 2 : ℂ) := by
    apply deriv_sub differentiableAt_digamma_half
    apply (differentiableAt_comp_const_sub (f := Complex.digamma) (a := (1 / 2 : ℂ)) (b := 1)).mpr
    have h2 : (1 : ℂ) - 1 / 2 = (1 / 2 : ℂ) := by norm_num only
    rw [h2]
    exact differentiableAt_digamma_half
  rw [hsplit] at hderiv_eq
  have hchain :
    deriv (fun z : ℂ => Complex.digamma (1 - z)) (1 / 2 : ℂ) =
      -deriv Complex.digamma (1 / 2 : ℂ) := by
    have h1 := deriv_comp_const_sub (f := Complex.digamma) (a := 1) (x := (1 / 2 : ℂ))
    have h2 : (1 : ℂ) - 1 / 2 = (1 / 2 : ℂ) := by norm_num only
    rwa [h2] at h1
  rw [hchain] at hderiv_eq
  linear_combination hderiv_eq / 2

theorem s_add_half_mem_ball_one {s : ℂ} (hs : s ∈ Metric.ball (1 / 2 : ℂ) (1 / 4)) :
    (s + 1 / 2) ∈ Metric.ball (1 : ℂ) (1 / 2) := by
  rw [Metric.mem_ball, dist_eq_norm] at hs ⊢
  have heq : (s + 1 / 2 - 1 : ℂ) = s - 1 / 2 := by ring
  rw [heq]
  linarith [hs]

theorem two_s_mem_ball_one {s : ℂ} (hs : s ∈ Metric.ball (1 / 2 : ℂ) (1 / 4)) :
    (2 * s) ∈ Metric.ball (1 : ℂ) (1 / 2) := by
  rw [Metric.mem_ball, dist_eq_norm] at hs ⊢
  have heq : (2 * s - 1 : ℂ) = 2 * (s - 1 / 2) := by ring
  rw [heq, norm_mul]
  norm_num only [Complex.norm_two]
  linarith only [hs]

/-- **Duplication formula, differentiated once**: `digamma s + digamma (s+1/2) =
2·digamma(2s) - 2·log 2`, on the ball where `s`, `s + 1/2`, `2s` all avoid nonpositive integers.
Same pattern as `PseudoPrime.AnalyticNumberTheory.Gamma.digamma_sub_digamma_one_sub_eq`,
using `Complex.Gamma_mul_Gamma_add_half`. -/
theorem digamma_duplication_eq {s : ℂ} (hs : s ∈ Metric.ball (1 / 2 : ℂ) (1 / 4)) :
    Complex.digamma s + Complex.digamma (s + 1 / 2) =
      2 * Complex.digamma (2 * s) - 2 * Complex.log 2 := by
  have hcasthalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast,
      Complex.ofReal_ofNat, Nat.cast_ofNat]
  have hcastone : ((1 : ℝ) : ℂ) = (1 : ℂ) := by norm_num only [Complex.ofReal_one]
  have hz1 : ∀ m : ℕ, s ≠ -m := by
    have h := ball_avoids_nonpos_int (c := 1 / 2) (r := 1 / 4) (by norm_num only) (by norm_num only)
    rw [hcasthalf] at h; exact h s hs
  have hz2 : ∀ m : ℕ, (s + 1 / 2) ≠ -m := by
    have h := ball_avoids_nonpos_int (c := 1) (r := 1 / 2) (by norm_num only) (by norm_num only)
    rw [hcastone] at h; exact h (s + 1 / 2) (s_add_half_mem_ball_one hs)
  have hz3 : ∀ m : ℕ, (2 * s) ≠ -m := by
    have h := ball_avoids_nonpos_int (c := 1) (r := 1 / 2) (by norm_num only) (by norm_num only)
    rw [hcastone] at h; exact h (2 * s) (two_s_mem_ball_one hs)
  have hGs : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hz1
  have hGs' : Complex.Gamma (s + 1 / 2) ≠ 0 := Complex.Gamma_ne_zero hz2
  have hG2s : Complex.Gamma (2 * s) ≠ 0 := Complex.Gamma_ne_zero hz3
  have hd1 : HasDerivAt Complex.Gamma (Complex.Gamma s * Complex.digamma s) s := by
    have heq : Complex.Gamma s * Complex.digamma s = deriv Complex.Gamma s := by
      rw [Complex.digamma_def, logDeriv_apply, mul_comm, div_mul_cancel₀ _ hGs]
    rw [heq]; exact (Complex.differentiableAt_Gamma s hz1).hasDerivAt
  have hd2 :
    HasDerivAt Complex.Gamma (Complex.Gamma (s + 1 / 2) * Complex.digamma (s + 1 / 2))
      (s + 1 / 2) := by
    have heq :
      Complex.Gamma (s + 1 / 2) * Complex.digamma (s + 1 / 2) =
        deriv Complex.Gamma (s + 1 / 2) := by
      rw [Complex.digamma_def, logDeriv_apply, mul_comm, div_mul_cancel₀ _ hGs']
    rw [heq]; exact (Complex.differentiableAt_Gamma (s + 1 / 2) hz2).hasDerivAt
  have hd3 :
    HasDerivAt Complex.Gamma (Complex.Gamma (2 * s) * Complex.digamma (2 * s)) (2 * s) := by
    have heq : Complex.Gamma (2 * s) * Complex.digamma (2 * s) = deriv Complex.Gamma (2 * s) := by
      rw [Complex.digamma_def, logDeriv_apply, mul_comm, div_mul_cancel₀ _ hG2s]
    rw [heq]; exact (Complex.differentiableAt_Gamma (2 * s) hz3).hasDerivAt
  have hd2' :
    HasDerivAt (fun w : ℂ => Complex.Gamma (w + 1 / 2))
      (Complex.Gamma (s + 1 / 2) * Complex.digamma (s + 1 / 2)) s :=
    hd2.comp_add_const s (1 / 2)
  have hd3' :
    HasDerivAt (fun w : ℂ => Complex.Gamma (2 * w))
      (Complex.Gamma (2 * s) * Complex.digamma (2 * s) * 2) s := by
    have h1 : HasDerivAt (fun w : ℂ => (2 : ℂ) * w) (2 : ℂ) s := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul (2 : ℂ)
    exact hd3.comp s h1
  have hprodL :
    HasDerivAt (fun w : ℂ => Complex.Gamma w * Complex.Gamma (w + 1 / 2))
      (Complex.Gamma s * Complex.digamma s * Complex.Gamma (s + 1 / 2) +
        Complex.Gamma s * (Complex.Gamma (s + 1 / 2) * Complex.digamma (s + 1 / 2)))
      s :=
    hd1.mul hd2'
  have hpow :
    HasDerivAt (fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w)) ((2 : ℂ) ^ (1 - 2 * s) * Complex.log 2 * (-2))
      s := by
    have h0 : HasDerivAt (fun w : ℂ => (2 : ℂ) * w) (2 : ℂ) s := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul (2 : ℂ)
    have h1 : HasDerivAt (fun w : ℂ => (1 : ℂ) - 2 * w) (-2 : ℂ) s := h0.const_sub (1 : ℂ)
    have h2 := h1.const_cpow (c := (2 : ℂ)) (Or.inl (by norm_num only))
    simpa only [mul_comm, mul_neg] using h2
  have hprodR :
    HasDerivAt (fun w : ℂ => Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) * Real.sqrt Real.pi)
      ((Complex.Gamma (2 * s) * Complex.digamma (2 * s) * 2 * (2 : ℂ) ^ (1 - 2 * s) +
          Complex.Gamma (2 * s) * ((2 : ℂ) ^ (1 - 2 * s) * Complex.log 2 * (-2))) *
        Real.sqrt Real.pi)
      s :=
    (hd3'.mul hpow).mul_const _
  have hcongr :
    (fun w : ℂ => Complex.Gamma w * Complex.Gamma (w + 1 / 2)) =
      (fun w : ℂ => Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) * Real.sqrt Real.pi) :=
    funext Complex.Gamma_mul_Gamma_add_half
  rw [hcongr] at hprodL
  have hEq := hprodL.unique hprodR
  have hdup :
    Complex.Gamma (2 * s) * (2 : ℂ) ^ (1 - 2 * s) * Real.sqrt Real.pi =
      Complex.Gamma s * Complex.Gamma (s + 1 / 2) :=
    (Complex.Gamma_mul_Gamma_add_half s).symm
  have hGnezero : Complex.Gamma s * Complex.Gamma (s + 1 / 2) ≠ 0 := mul_ne_zero hGs hGs'
  have key :
    Complex.Gamma s * Complex.Gamma (s + 1 / 2) *
        (Complex.digamma s + Complex.digamma (s + 1 / 2)) =
      Complex.Gamma s * Complex.Gamma (s + 1 / 2) *
        (2 * Complex.digamma (2 * s) - 2 * Complex.log 2) := by
    have hfactorL :
      Complex.Gamma s * Complex.digamma s * Complex.Gamma (s + 1 / 2) +
          Complex.Gamma s * (Complex.Gamma (s + 1 / 2) * Complex.digamma (s + 1 / 2)) =
        Complex.Gamma s * Complex.Gamma (s + 1 / 2) *
          (Complex.digamma s + Complex.digamma (s + 1 / 2)) := by
      ring
    rw [hfactorL] at hEq
    rw [hEq]
    rw [← hdup]
    ring
  exact mul_left_cancel₀ hGnezero key

/-- `digamma'(1) = π²/6`, obtained by differentiating the digamma duplication
identity once at `1/2` and substituting `digamma'(1/2) = π²/2`. -/
theorem deriv_digamma_one_eq : deriv Complex.digamma (1 : ℂ) = (Real.pi : ℂ) ^ 2 / 6 := by
  have heventually :
    (fun s : ℂ => Complex.digamma s + Complex.digamma (s + 1 / 2)) =ᶠ[nhds (1 / 2 : ℂ)]
      (fun s : ℂ => 2 * Complex.digamma (2 * s) - 2 * Complex.log 2) := by
    filter_upwards [Metric.ball_mem_nhds (1 / 2 : ℂ) (by norm_num only : (0 : ℝ) < 1 / 4)] with s hs
    exact digamma_duplication_eq hs
  have h2half1 : (2 : ℂ) * (1 / 2 : ℂ) = 1 := by norm_num only
  have h1half1 : (1 / 2 : ℂ) + 1 / 2 = (1 : ℂ) := by norm_num only
  have hLcomp :
    HasDerivAt (fun s : ℂ => Complex.digamma (s + 1 / 2)) (deriv Complex.digamma 1)
      (1 / 2 : ℂ) := by
    have hdiff' : DifferentiableAt ℂ Complex.digamma (1 / 2 + 1 / 2 : ℂ) := by
      rw [h1half1]; exact differentiableAt_digamma_one
    have hcomp := hdiff'.hasDerivAt.comp_add_const (1 / 2 : ℂ) (1 / 2 : ℂ)
    have hval : deriv Complex.digamma (1 / 2 + 1 / 2 : ℂ) = deriv Complex.digamma 1 := by
      rw [h1half1]
    rwa [hval] at hcomp
  have hL :
    HasDerivAt (fun s : ℂ => Complex.digamma s + Complex.digamma (s + 1 / 2))
      (deriv Complex.digamma (1 / 2 : ℂ) + deriv Complex.digamma 1) (1 / 2 : ℂ) :=
    differentiableAt_digamma_half.hasDerivAt.add hLcomp
  have hRcomp :
    HasDerivAt (fun s : ℂ => Complex.digamma (2 * s)) (deriv Complex.digamma 1 * 2)
      (1 / 2 : ℂ) := by
    have hdiff' : DifferentiableAt ℂ Complex.digamma (2 * (1 / 2 : ℂ)) := by
      rw [h2half1]; exact differentiableAt_digamma_one
    have h1 : HasDerivAt (fun s : ℂ => (2 : ℂ) * s) (2 : ℂ) (1 / 2 : ℂ) := by
      simpa only [one_div, id_eq, mul_one] using (hasDerivAt_id (1 / 2 : ℂ)).const_mul (2 : ℂ)
    have hcomp := hdiff'.hasDerivAt.comp (1 / 2 : ℂ) h1
    have hval : deriv Complex.digamma (2 * (1 / 2 : ℂ)) = deriv Complex.digamma 1 := by rw [h2half1]
    rwa [hval] at hcomp
  have hR :
    HasDerivAt (fun s : ℂ => 2 * Complex.digamma (2 * s) - 2 * Complex.log 2)
      (2 * (deriv Complex.digamma 1 * 2)) (1 / 2 : ℂ) := by
    have h1 :
      HasDerivAt (fun s : ℂ => 2 * Complex.digamma (2 * s)) (2 * (deriv Complex.digamma 1 * 2))
        (1 / 2 : ℂ) :=
      hRcomp.const_mul 2
    simpa only [one_div, hasDerivAt_sub_const_iff] using h1.sub_const (2 * Complex.log 2)
  have hRcongr :
    HasDerivAt (fun s : ℂ => Complex.digamma s + Complex.digamma (s + 1 / 2))
      (2 * (deriv Complex.digamma 1 * 2)) (1 / 2 : ℂ) :=
    hR.congr_of_eventuallyEq heventually
  have hUnique := hL.unique hRcongr
  linear_combination deriv_digamma_half_eq / 3 - hUnique / 3

end PseudoPrime.AnalyticNumberTheory.Gamma
