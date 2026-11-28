/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddlePrincipalAbel
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalZeroCancel
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalLogMoments
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogZeroIntegration

/-! # Integrals of the anchored logarithmic zero terms -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The real nontrivial-zero contribution to the logarithmically weighted Mangoldt sum. -/
@[expose]
public noncomputable def middleZeroPart (t : ℝ) : ℝ :=
  (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re

/-- Separate the nontrivial and trivial zero contributions in the anchored weighted error. -/
public theorem middle_anchored_integral_split {T : ℝ} (hT : 1 ≤ T) {Q : ℝ → ℝ}
    (hQ : ContinuousOn Q (Set.Icc 1 T)) :
    (∫ t in (1 : ℝ)..T,
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
              (t - Real.log (2 * Real.pi) * Real.log t) +
            1) *
          Q t) =
      (∫ t in (1 : ℝ)..T, (middleZeroPart t - middleZeroPart 1) * Q t) -
        ∫ t in (1 : ℝ)..T,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t -
              AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries 1) *
            Q t := by
  have hz : ContinuousOn middleZeroPart (Set.Icc 1 T) :=
    Complex.continuous_re.continuousOn.comp
      (AnalyticNumberTheory.RiemannZeta.zero_sum_continuous le_rfl) (fun _ _ ↦ Set.mem_univ _)
  have ht := AnalyticNumberTheory.RiemannZeta.trivial_cont_closed (b := T) le_rfl
  have hi :
    IntervalIntegrable (fun t ↦ (middleZeroPart t - middleZeroPart 1) * Q t) MeasureTheory.volume 1
      T :=
    ((hz.sub continuousOn_const).mul hQ).intervalIntegrable_of_Icc hT
  have hj :
    IntervalIntegrable
      (fun t ↦
        (AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t -
            AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries 1) *
          Q t)
      MeasureTheory.volume 1 T :=
    ((ht.sub continuousOn_const).mul hQ).intervalIntegrable_of_Icc hT
  rw [←
    intervalIntegral.integral_sub (f := fun t ↦ (middleZeroPart t - middleZeroPart 1) * Q t) hi hj]
  apply intervalIntegral.integral_congr
  intro t ht'
  have ha := (Set.uIcc_of_le hT ▸ ht').1
  simp only [middle_anchored_explicit ha, sub_mul, middleZeroPart]

/-- The existing finite zero ledgers converge after multiplying by a continuous
weight, integrating over `[1,T]`, and subtracting the fixed anchoring term. -/
public theorem middle_anchored_zero_integral_limit {T : ℝ} (hT : 1 ≤ T) {Q : ℝ → ℝ}
    (hQ : ContinuousOn Q (Set.Icc 1 T)) :
    Filter.Tendsto
      (fun m : ℕ ↦
        ∫ x in (1 : ℝ)..T,
          ((∑
                  ρ ∈
                    (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
                          (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower m)
                          (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
                      (fun ρ ↦ ¬ρ.re < 0),
                  AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution x ρ).re -
              middleZeroPart 1) *
            Q x)
      Filter.atTop (nhds (∫ x in (1 : ℝ)..T, (middleZeroPart x - middleZeroPart 1) * Q x)) := by
  classical
  let S : ℕ → Finset ℂ := fun m ↦
    (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
          (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower m)
          (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
      (fun ρ ↦ ¬ρ.re < 0)
  let F (m : ℕ) (x : ℝ) : ℝ :=
    (∑ ρ ∈ S m, AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution x ρ).re
  have hF (m : ℕ) : ContinuousOn (F m) (Set.Icc 1 T) := by
    apply Complex.continuous_re.continuousOn.comp _ (fun _ _ ↦ Set.mem_univ _)
    apply continuousOn_finsetSum
    intro ρ hρ
    have hm := Finset.mem_filter.mp hρ
    have hz := (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp hm.1).2
    simpa only [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, hz, true_and,
      not_lt.mp hm.2, ite_true] using
      (AnalyticNumberTheory.RiemannZeta.zero_term_continuous (a := 1) (b := T) zero_lt_one ρ)
  have hz : ContinuousOn middleZeroPart (Set.Icc 1 T) :=
    Complex.continuous_re.continuousOn.comp
      (AnalyticNumberTheory.RiemannZeta.zero_sum_continuous le_rfl) (fun _ _ ↦ Set.mem_univ _)
  have hc : IntervalIntegrable (fun x ↦ middleZeroPart 1 * Q x) MeasureTheory.volume 1 T :=
    (continuousOn_const.mul hQ).intervalIntegrable_of_Icc hT
  have h :=
    (AnalyticNumberTheory.RiemannZeta.weighted_zero_integral_limit le_rfl hT hQ).sub
      (tendsto_const_nhds (x := ∫ x in (1 : ℝ)..T, middleZeroPart 1 * Q x))
  change
    Filter.Tendsto
      (fun m ↦ (∫ x in (1 : ℝ)..T, F m x * Q x) - ∫ x in (1 : ℝ)..T, middleZeroPart 1 * Q x)
      Filter.atTop
      (nhds
        ((∫ x in (1 : ℝ)..T, middleZeroPart x * Q x) -
          ∫ x in (1 : ℝ)..T, middleZeroPart 1 * Q x)) at h
  rw [←
    intervalIntegral.integral_sub (f := fun x ↦ middleZeroPart x * Q x)
      ((hz.mul hQ).intervalIntegrable_of_Icc hT) hc] at h
  simp only [← sub_mul] at h
  apply h.congr'
  filter_upwards with m
  rw [←
    intervalIntegral.integral_sub (f := fun x ↦ F m x * Q x)
      (((hF m).mul hQ).intervalIntegrable_of_Icc hT) hc]
  simp only [← sub_mul]
  rfl

/-- Remove a fixed anchoring value from the principal functional on `[1,Z]`.
Only the lower edge remains when the differentiated weight vanishes at `Z`. -/
public theorem middle_principal_deanchor {P g : ℝ → ℝ} {X Z : ℝ} (hX : 1 ≤ X) (hXZ : X ≤ Z)
    (hP : ∀ t ∈ Set.Icc 1 Z, DifferentiableAt ℝ P t) (hQ : ContinuousOn (deriv P) (Set.Icc 1 Z))
    (hg : ContinuousOn g (Set.Icc 1 Z)) (hZ : P Z = 0) :
    (4 * (∫ t in (1 : ℝ)..X, (g t - g 1) * deriv P t) -
        (∫ t in (1 : ℝ)..Z, (g t - g 1) * deriv P t) -
        4 * (P X * (g X - g 1))) =
      4 * (∫ t in (1 : ℝ)..X, g t * deriv P t) - (∫ t in (1 : ℝ)..Z, g t * deriv P t) -
          4 * (P X * g X) +
        3 * (P 1 * g 1) := by
  have h (r : ℝ) (hr : 1 ≤ r) (hrZ : r ≤ Z) :
    (∫ t in (1 : ℝ)..r, (g t - g 1) * deriv P t) =
      (∫ t in (1 : ℝ)..r, g t * deriv P t) - g 1 * (P r - P 1) := by
    have hs : Set.Icc (1 : ℝ) r ⊆ Set.Icc 1 Z := Set.Icc_subset_Icc_right hrZ
    have hq := hQ.mono hs
    have hi : IntervalIntegrable (deriv P) MeasureTheory.volume 1 r :=
      hq.intervalIntegrable_of_Icc hr
    have hj : IntervalIntegrable (fun t ↦ g t * deriv P t) MeasureTheory.volume 1 r :=
      ((hg.mono hs).mul hq).intervalIntegrable_of_Icc hr
    have hd :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht ↦ (hP t (hs (Set.uIcc_of_le hr ▸ ht))).hasDerivAt) hi
    simp only [sub_mul]
    rw [intervalIntegral.integral_sub (f := fun t ↦ g t * deriv P t) hj (hi.const_mul _),
      intervalIntegral.integral_const_mul, hd]
  rw [h X hX hXZ, h Z (hX.trans hXZ) le_rfl, hZ]
  ring

/-- The unscaled truncated principal functional combines two integrals and the
shared cutoff boundary value of the logarithmic remainder. -/
@[expose]
public noncomputable def middleTruncPrincipal (P g : ℝ → ℝ) (X Z : ℝ) : ℝ :=
  4 * (∫ t in (1 : ℝ)..X, g t * deriv P t) - (∫ t in (1 : ℝ)..Z, g t * deriv P t) - 4 * (P X * g X)

/-- Split the truncated anchored principal error into unanchored spectral
contributions and one explicit correction at the lower edge. -/
public theorem middle_trunc_principal_split {P : ℝ → ℝ} {X Z : ℝ} (hX : 1 ≤ X) (hXZ : X ≤ Z)
    (hP : ∀ t ∈ Set.Icc 1 Z, DifferentiableAt ℝ P t) (hQ : ContinuousOn (deriv P) (Set.Icc 1 Z))
    (hZ : P Z = 0) :
    let H := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
          (t - Real.log (2 * Real.pi) * Real.log t) +
        1
    let G := AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries
    middleTruncPrincipal P H X Z =
      middleTruncPrincipal P middleZeroPart X Z - middleTruncPrincipal P G X Z +
        3 * (P 1 * (middleZeroPart 1 - G 1)) := by
  intro H G
  have hz : ContinuousOn middleZeroPart (Set.Icc 1 Z) :=
    Complex.continuous_re.continuousOn.comp
      (AnalyticNumberTheory.RiemannZeta.zero_sum_continuous le_rfl) (fun _ _ ↦ Set.mem_univ _)
  have hg : ContinuousOn G (Set.Icc 1 Z) :=
    AnalyticNumberTheory.RiemannZeta.trivial_cont_closed le_rfl
  have hx :=
    middle_anchored_integral_split hX
      (hQ.mono (show Set.Icc 1 X ⊆ Set.Icc 1 Z from Set.Icc_subset_Icc_right hXZ))
  have hu := middle_anchored_integral_split (hX.trans hXZ) hQ
  have ha := middle_principal_deanchor hX hXZ hP hQ hz hZ
  have hb := middle_principal_deanchor hX hXZ hP hQ hg hZ
  have he : H X = (middleZeroPart X - middleZeroPart 1) - (G X - G 1) := middle_anchored_explicit hX
  change (∫ t in (1 : ℝ)..X, H t * deriv P t) = _ at hx
  change (∫ t in (1 : ℝ)..Z, H t * deriv P t) = _ at hu
  rw [middleTruncPrincipal, hx, hu, he, middleTruncPrincipal, middleTruncPrincipal]
  simp only [mul_sub]
  linarith only [ha, hb]

/-- Changing variables from the physical scale to the unit cutoff in an
integral with a derivative weight. -/
private theorem middle_principal_integral_scale {P F g : ℝ → ℝ} {X k a b : ℝ} (hX : 0 < X)
    (ha : 0 ≤ a) (hab : a ≤ b) (hQ : ∀ u > 0, deriv P (X * u) = (k / X) * deriv F u) :
    (∫ t in (X * a)..(X * b), g t * deriv P t) = k * ∫ u in a..b, g (X * u) * deriv F u := by
  let f := fun t ↦ g t * deriv P t
  have he : (∫ u in a..b, f (X * u)) = (k / X) * ∫ u in a..b, g (X * u) * deriv F u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro u hu
    dsimp only [f]
    rw [hQ u (ha.trans_lt hu.1)]
    ring
  have hh : (∫ u in a..b, f (X * u)) = X⁻¹ * ∫ t in (X * a)..(X * b), f t := by
    simpa only [smul_eq_mul, mul_comm X a, mul_comm X b, mul_comm X _] using
      intervalIntegral.integral_comp_mul_right f (a := a) (b := b) hX.ne'
  rw [he] at hh
  have h := congrArg (fun v : ℝ ↦ X * v) hh.symm
  simpa only [← mul_assoc, mul_inv_cancel₀ hX.ne', one_mul, mul_div_cancel₀ _ hX.ne'] using h

/-- Extend the rescaled truncated functional down to zero, recording the
integral removed below the physical endpoint one. -/
public theorem middle_trunc_principal_scale {P F g : ℝ → ℝ} {X y k : ℝ} (hX : 1 ≤ X) (hy : 1 ≤ y)
    (hP : P X = k * F 1) (hQ : ∀ u > 0, deriv P (X * u) = (k / X) * deriv F u)
    (hi : IntervalIntegrable (fun u ↦ g (X * u) * deriv F u) MeasureTheory.volume 0 1)
    (hj : IntervalIntegrable (fun u ↦ g (X * u) * deriv F u) MeasureTheory.volume 1 y) :
    middleTruncPrincipal P g X (X * y) =
      k *
        (principalErrorFunctional (deriv F) g (F 1) X y -
          3 * ∫ u in (0 : ℝ)..1 / X, g (X * u) * deriv F u) := by
  have hp := zero_lt_one.trans_le hX
  have h₀ : 0 ≤ 1 / X := one_div_nonneg.mpr hp.le
  have h₁ : 1 / X ≤ 1 := (div_le_iff₀ hp).mpr (by simpa only [one_mul] using hX)
  let f := fun u ↦ g (X * u) * deriv F u
  have hl : IntervalIntegrable f MeasureTheory.volume 0 (1 / X) :=
    hi.mono_set
      (by
        rw [Set.uIcc_of_le h₀, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc_right h₁)
  have hr : IntervalIntegrable f MeasureTheory.volume (1 / X) 1 :=
    hi.mono_set
      (by
        rw [Set.uIcc_of_le h₁, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc_left h₀)
  have ha := middle_principal_integral_scale (P := P) (F := F) (g := g) hp h₀ h₁ hQ
  have hb := middle_principal_integral_scale (P := P) (F := F) (g := g) hp h₀ (h₁.trans hy) hQ
  rw [mul_one, mul_one_div_cancel hp.ne'] at ha
  rw [mul_one_div_cancel hp.ne'] at hb
  have hd := intervalIntegral.integral_add_adjacent_intervals hl hr
  have he := intervalIntegral.integral_add_adjacent_intervals hr hj
  rw [middleTruncPrincipal, ha, hb, hP, principalErrorFunctional]
  dsimp only [f] at hd he
  rw [← hd, ← he]
  ring

/-- The physical nontrivial-zero functional is the cancelled zero series,
scaled by the physical weight and with its integral below one removed. -/
public theorem middle_principal_zero_series (B : Polynomial ℝ) (k : ℝ) (hRH : RiemannHypothesis)
    {d b X : ℝ} (hd : 0 < d) (hb : 0 < b) (hX : 1 ≤ X) (hB : B.eval 0 = 0)
    (hB' : B.derivative.eval 0 = 0) :
    let W := middlePrincipalWeight B k (Real.log X + b) d
    let P := fun t ↦ t * deriv W t
    let V := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    let F := fun u ↦ u * deriv V u
    middleTruncPrincipal P middleZeroPart X (X * Real.exp b) =
      (k * X ^ d) *
        (Real.sqrt X * (∑' ρ, principalCancelledTerm B d b X ρ) -
          3 * ∫ u in (0 : ℝ)..1 / X, middleZeroPart (X * u) * deriv F u) := by
  intro W P V F
  have hp := zero_lt_one.trans_le hX
  have hy := Real.one_le_exp hb.le
  have hs := middle_principal_weight_scale B k d b hp
  have hi := reflected_principal_integrable B hd hb
  change
    IntervalIntegrable (deriv F) MeasureTheory.volume 0 1 ∧
      IntervalIntegrable (deriv F) MeasureTheory.volume 1 (Real.exp b) at hi
  have hc : ContinuousOn (fun u ↦ middleZeroPart (X * u)) (Set.Icc 0 (Real.exp b)) :=
    gaussian_log_zero_scaled_continuous hRH hp _
  have ha :=
    hi.1.mul_continuousOn
      (by
        rw [Set.uIcc_of_le zero_le_one]; exact hc.mono (Set.Icc_subset_Icc_right hy))
  have hz :=
    hi.2.mul_continuousOn
      (by
        rw [Set.uIcc_of_le hy]; exact hc.mono (Set.Icc_subset_Icc_left zero_le_one))
  have ht :=
    middle_trunc_principal_scale (P := P) (F := F) (g := middleZeroPart) hX hy
      (by simpa only [mul_one] using hs.1 1 zero_lt_one) hs.2
      (by simpa only [mul_comm (deriv F _)] using ha)
      (by simpa only [mul_comm (deriv F _)] using hz)
  have he := (principal_cancelled_hasSum B hRH hd hb hp hB hB').tsum_eq
  change
    (∑' ρ, principalCancelledTerm B d b X ρ) =
      principalErrorFunctional (deriv F) middleZeroPart (F 1) X (Real.exp b) / Real.sqrt X at he
  rw [ht, he, mul_div_cancel₀ _ (Real.sqrt_pos.2 hp).ne']

/-- The correction below the physical endpoint one is bounded by the absolute
derivative moment on the corresponding reciprocal-cutoff interval. -/
public theorem middle_zero_lower_moment (Q : ℝ → ℝ) (hRH : RiemannHypothesis) {X : ℝ} (hX : 0 < X)
    (hQ : IntervalIntegrable Q MeasureTheory.volume 0 (1 / X)) :
    |∫ u in (0 : ℝ)..1 / X, middleZeroPart (X * u) * Q u| ≤
      (231 / 5000 : ℝ) * ∫ u in (0 : ℝ)..1 / X, |Q u| := by
  rw [← Real.norm_eq_abs, ← intervalIntegral.integral_const_mul]
  refine
    intervalIntegral.norm_integral_le_of_norm_le (one_div_nonneg.mpr hX.le) ?_ (hQ.abs.const_mul _)
  filter_upwards with u hu
  rw [Real.norm_eq_abs, abs_mul]
  have hle : X * u ≤ 1 := by
    calc
      X * u ≤ X * (1 / X) := mul_le_mul_of_nonneg_left hu.2 hX.le
      _ = 1 := mul_one_div_cancel hX.ne'
  have hz := gaussian_log_zero_abs_le hRH (mul_pos hX hu.1)
  have hs : Real.sqrt (X * u) ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hle
  exact
    mul_le_mul_of_nonneg_right
      (hz.trans
        (by
          calc
            _ ≤ (231 / 5000 : ℝ) * 1 := mul_le_mul_of_nonneg_left hs (by norm_num only)
            _ = _ := mul_one _))
      (abs_nonneg _)

/-- At the omitted physical arguments between zero and one, the clipped
arithmetic remainder is exactly minus its argument. -/
private theorem middle_clipped_low {t : ℝ} (ht : t ≤ 1) : gaussianLogZetaError t = -t := by
  rw [gaussianLogZetaError, LLS.logWeightedMangoldtSum_eq_zero_of_le_one ht, max_eq_left ht,
    Real.log_one, mul_zero, add_zero, zero_sub]

/-- Below one, the clipped correction cancels the linear term of the remainder.
After subtracting the constant, the surviving term has square-root decay. -/
public theorem middle_low_remainder_decay (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 < t)
    (h₁ : t ≤ 1) :
    |gaussianLogZetaRemainder t + t - gaussianLogZetaConstant| ≤ 231 / 5000 * Real.sqrt t := by
  have h := gaussian_log_error_split t
  rw [middle_clipped_low h₁] at h
  rw [show gaussianLogZetaRemainder t + t - gaussianLogZetaConstant = -gaussianLogZetaZeroSum t by
      linarith only [h],
    abs_neg]
  exact gaussian_log_zero_abs_le hRH ht

/-- The low-argument remainder after cancellation uses the absolute derivative
moment weighted by the square root of the physical argument. -/
public theorem middle_low_remainder_integral (Q : ℝ → ℝ) (hRH : RiemannHypothesis) {X : ℝ}
    (hX : 0 < X) (hQ : IntervalIntegrable Q MeasureTheory.volume 0 X⁻¹) :
    |∫ u in (0 : ℝ)..X⁻¹,
          (gaussianLogZetaRemainder (X * u) + X * u - gaussianLogZetaConstant) * Q u| ≤
      (231 / 5000 : ℝ) * ∫ u in (0 : ℝ)..X⁻¹, Real.sqrt (X * u) * |Q u| := by
  have hc : Continuous (fun u : ℝ ↦ Real.sqrt (X * u)) :=
    Real.continuous_sqrt.comp (continuous_const.mul continuous_id)
  rw [← Real.norm_eq_abs, ← intervalIntegral.integral_const_mul]
  refine
    intervalIntegral.norm_integral_le_of_norm_le (inv_nonneg.mpr hX.le) ?_
      ((hQ.abs.continuousOn_mul hc.continuousOn).const_mul _)
  filter_upwards with u hu
  rw [Real.norm_eq_abs, abs_mul, ← mul_assoc]
  have he := (mul_le_mul_of_nonneg_left hu.2 hX.le).trans_eq (mul_inv_cancel₀ hX.ne')
  exact
    mul_le_mul_of_nonneg_right (middle_low_remainder_decay hRH (mul_pos hX hu.1) he) (abs_nonneg _)

/-- Removing the anchor at one replaces it by an explicit lower boundary term
and leaves the clipped arithmetic error on the physical integration interval. -/
private theorem middle_anchored_to_clipped {P : ℝ → ℝ} {X Z : ℝ} (hX : 1 ≤ X) (hXZ : X ≤ Z)
    (hP : ∀ t ∈ Set.Icc 1 Z, DifferentiableAt ℝ P t) (hQ : ContinuousOn (deriv P) (Set.Icc 1 Z))
    (hZ : P Z = 0) :
    let H := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
          (t - Real.log (2 * Real.pi) * Real.log t) +
        1
    middleTruncPrincipal P H X Z = middleTruncPrincipal P gaussianLogZetaError X Z - 3 * P 1 := by
  intro H
  have he (t : ℝ) (ht : 1 ≤ t) : H t = gaussianLogZetaError t - gaussianLogZetaError 1 := by
    rw [gaussianLogZetaError, max_eq_right ht, middle_clipped_low le_rfl]
    dsimp only [H]
    ring
  have hi (r : ℝ) (hr : 1 ≤ r) :
    (∫ t in (1 : ℝ)..r, H t * deriv P t) =
      ∫ t in (1 : ℝ)..r, (gaussianLogZetaError t - gaussianLogZetaError 1) * deriv P t := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [he t (Set.uIcc_of_le hr ▸ ht).1]
  have hg : ContinuousOn gaussianLogZetaError (Set.Icc 1 Z) := by
    have h := gaussian_log_error_continuous (X := 1) zero_lt_one Z
    simp only [one_mul] at h
    exact h.mono (Set.Icc_subset_Icc_left zero_le_one)
  rw [middleTruncPrincipal, hi X hX, hi Z (hX.trans hXZ), he X hX,
    middle_principal_deanchor hX hXZ hP hQ hg hZ, middleTruncPrincipal, middle_clipped_low le_rfl]
  ring

/-- Reduce the full anchored principal error to the cancelled zero series,
the normalized remainder, and explicit terms from the physical lower edge. -/
public theorem middle_principal_error_series (B : Polynomial ℝ) (k : ℝ) (hRH : RiemannHypothesis)
    {d b X : ℝ} (hd : 0 < d) (hb : 0 < b) (hX : 1 ≤ X) (hB : B.eval 0 = 0)
    (hB' : B.derivative.eval 0 = 0) :
    let W := middlePrincipalWeight B k (Real.log X + b) d
    let P := fun t ↦ t * deriv W t
    let V := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    let F := fun u ↦ u * deriv V u
    let H := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
          (t - Real.log (2 * Real.pi) * Real.log t) +
        1
    middleTruncPrincipal P H X (X * Real.exp b) =
      (k * X ^ d) *
          (Real.sqrt X * (∑' ρ, principalCancelledTerm B d b X ρ) +
            principalErrorFunctional (deriv F) gaussianLogZetaRemainder (F 1) X (Real.exp b) +
            3 * (∫ u in (0 : ℝ)..X⁻¹, (X * u - gaussianLogZetaConstant) * deriv F u)) +
        3 * (gaussianLogZetaConstant - 1) * P 1 := by
  intro W P V F H
  have hp := zero_lt_one.trans_le hX
  have hy := Real.one_le_exp hb.le
  have hxy : X ≤ X * Real.exp b := le_mul_of_one_le_right hp.le hy
  have hZ : X * Real.exp b = Real.exp (Real.log X + b) := by rw [Real.exp_add, Real.exp_log hp]
  have he : P (X * Real.exp b) = 0 := by
    dsimp only [P, W]
    rw [hZ, (middle_principal_upper_jet B k (Real.log X + b) d hB hB').2, mul_zero]
  have hdP t (ht : t ∈ Set.Icc 1 (X * Real.exp b)) : DifferentiableAt ℝ P t :=
    (middle_principal_moment_deriv B k (Real.log X + b) d
        (zero_lt_one.trans_le ht.1)).differentiableAt
  have hQ :=
    (middle_principal_moment_cont B k (Real.log X + b) d).mono
      (show Set.Icc 1 (X * Real.exp b) ⊆ Set.Ioi 0 from fun _ ht ↦ zero_lt_one.trans_le ht.1)
  have hclip := middle_anchored_to_clipped hX hxy hdP hQ he
  have hs := middle_principal_weight_scale B k d b hp
  have hi := reflected_principal_integrable B hd hb
  change
    IntervalIntegrable (deriv F) MeasureTheory.volume 0 1 ∧
      IntervalIntegrable (deriv F) MeasureTheory.volume 1 (Real.exp b) at hi
  have hc := gaussian_log_error_continuous hp (Real.exp b)
  have ha :=
    hi.1.continuousOn_mul
      (by
        rw [Set.uIcc_of_le zero_le_one]; exact hc.mono (Set.Icc_subset_Icc_right hy))
  have hz :=
    hi.2.continuousOn_mul
      (by
        rw [Set.uIcc_of_le hy]; exact hc.mono (Set.Icc_subset_Icc_left zero_le_one))
  have ht :=
    middle_trunc_principal_scale (P := P) (F := F) (g := gaussianLogZetaError) hX hy
      (by simpa only [mul_one] using hs.1 1 zero_lt_one) hs.2 ha hz
  have hlow :
    (∫ u in (0 : ℝ)..1 / X, gaussianLogZetaError (X * u) * deriv F u) =
      -(∫ u in (0 : ℝ)..1 / X, (X * u) * deriv F u) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_Ioo_of_le (one_div_nonneg.mpr hp.le)
    intro u hu
    have hu' : X * u ≤ 1 := by
      calc
        X * u ≤ X * (1 / X) := mul_le_mul_of_nonneg_left hu.2.le hp.le
        _ = 1 := mul_one_div_cancel hp.ne'
    dsimp only
    rw [middle_clipped_low hu', neg_mul]
  have hsplit := reflected_principal_error_split B hRH hd hb hp hB hB'
  have hsum := (principal_cancelled_hasSum B hRH hd hb hp hB hB').tsum_eq
  change
    (∑' ρ, principalCancelledTerm B d b X ρ) =
      principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp b) /
        Real.sqrt X at hsum
  change middleTruncPrincipal P H X (X * Real.exp b) = _ at hclip
  rw [hclip, ht, hlow, hsplit, hsum, mul_div_cancel₀ _ (Real.sqrt_pos.2 hp).ne']
  have hc₀ : 0 < X⁻¹ := inv_pos.mpr hp
  have hc₁ : X⁻¹ ≤ 1 := (inv_le_one₀ hp).mpr hX
  have hsmall :=
    hi.1.mono_set
      (show Set.uIcc 0 X⁻¹ ⊆ Set.uIcc 0 (1 : ℝ) from by
        rw [Set.uIcc_of_le hc₀.le, Set.uIcc_of_le zero_le_one]
        exact Set.Icc_subset_Icc_right hc₁)
  have hlin : Continuous (fun u : ℝ ↦ X * u) := continuous_const.mul continuous_id
  have hcut := hsmall.continuousOn_mul hlin.continuousOn
  have hInt :
    (∫ u in (0 : ℝ)..X⁻¹, (X * u - gaussianLogZetaConstant) * deriv F u) =
      (∫ u in (0 : ℝ)..X⁻¹, (X * u) * deriv F u) - gaussianLogZetaConstant * F X⁻¹ := by
    simp only [sub_mul]
    rw [intervalIntegral.integral_sub hcut (hsmall.const_mul _),
      intervalIntegral.integral_const_mul, reflected_principal_integral_zero B hd hc₀ hsmall]
  have heq := hs.1 X⁻¹ hc₀
  rw [mul_inv_cancel₀ hp.ne'] at heq
  change P 1 = (k * X ^ d) * F X⁻¹ at heq
  rw [one_div, hInt, heq]
  ring

/-- The square-root weight increases the logarithmic tail's exponential
decay rate from `d` to `d + 1/2`. -/
public theorem middle_low_sqrt_moment (D : Polynomial ℝ) (d b : ℝ) {X : ℝ} (hX : 0 < X) :
    (∫ u in (0 : ℝ)..X⁻¹, Real.sqrt (X * u) * (u ^ (d - 1) * |D.eval (b - Real.log u)|)) =
      Real.sqrt X *
        ∫ t in Set.Ioi (Real.log X), Real.exp (-(d + 1 / 2) * t) * |D.eval (b + t)| := by
  rw [← reflected_low_abs_moment D (d + 1 / 2) b hX, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le (inv_nonneg.mpr hX.le)
  intro u hu
  dsimp only
  rw [Real.sqrt_mul hX.le, mul_assoc, ← mul_assoc (Real.sqrt u), Real.sqrt_eq_rpow u, ←
    Real.rpow_add hu.1]
  rw [show (1 / 2 : ℝ) + (d - 1) = d + 1 / 2 - 1 by ring]

/-- The joint remainder after removing the low-argument constant has one
square-root-weighted low moment and one inverse-square high moment. -/
public theorem middle_principal_decay (Q : ℝ → ℝ) (hRH : RiemannHypothesis) {X y edge : ℝ}
    (hX : 1 ≤ X) (hy : 1 ≤ y) (h₁ : IntervalIntegrable Q MeasureTheory.volume 0 1)
    (h₂ : IntervalIntegrable Q MeasureTheory.volume 1 y) :
    let c := X⁻¹
    |principalErrorFunctional Q gaussianLogZetaRemainder edge X y +
          3 * (∫ u in (0 : ℝ)..c, (X * u - gaussianLogZetaConstant) * Q u)| ≤
      693 / 5000 * (∫ u in (0 : ℝ)..c, Real.sqrt (X * u) * |Q u|) +
        5 / 4 * c ^ 2 * (∫ u in c..y, u⁻¹ ^ 2 * |Q u|) +
        5 / 3 * |edge| * c ^ 2 := by
  intro c
  have hp := zero_lt_one.trans_le hX
  have hc : 0 < c := inv_pos.mpr hp
  have hle : c ≤ 1 := (inv_le_one₀ hp).mpr hX
  have hXa : X * c = 1 := mul_inv_cancel₀ hp.ne'
  have hsub₀ : Set.uIcc 0 c ⊆ Set.uIcc 0 (1 : ℝ) := by
    rw [Set.uIcc_of_le hc.le, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc_right hle
  have hsub₁ : Set.uIcc c 1 ⊆ Set.uIcc 0 (1 : ℝ) := by
    rw [Set.uIcc_of_le hle, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc_left hc.le
  have hq₀ := h₁.mono_set hsub₀
  have hq₁ := h₁.mono_set hsub₁
  let G := fun u ↦ gaussianLogZetaRemainder (X * u)
  have hG : IntervalIntegrable (fun u ↦ G u * Q u) MeasureTheory.volume 0 1 :=
    h₁.continuousOn_mul
      (by
        rw [Set.uIcc_of_le zero_le_one]
        exact gaussian_log_remainder_continuous hRH hp 1)
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals (hG.mono_set hsub₀) (hG.mono_set hsub₁)
  have hlin : Continuous (fun u : ℝ ↦ X * u - gaussianLogZetaConstant) :=
    (continuous_const.mul continuous_id).sub continuous_const
  have hlow := abs_le.mp (middle_low_remainder_integral Q hRH hp hq₀)
  have hhigh := abs_le.mp (principal_rem_high hp hc hle hXa.ge hq₁)
  have htop := abs_le.mp (principal_rem_high hp zero_lt_one hy (by rwa [mul_one]) h₂)
  have hInv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun u : ℝ ↦ u⁻¹ ^ 2) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    have hId : ContinuousOn (fun u : ℝ ↦ u) (Set.Icc a b) := continuousOn_id
    exact (hId.inv₀ (fun _ hu ↦ (ha.trans_le hu.1).ne')).pow 2
  have hAdd :=
    intervalIntegral.integral_add_adjacent_intervals (hq₁.abs.continuousOn_mul (hInv hc hle))
      (h₂.abs.continuousOn_mul (hInv zero_lt_one hy))
  have hnn : 0 ≤ (5 / 12 : ℝ) * c ^ 2 * (∫ u in (1 : ℝ)..y, u⁻¹ ^ 2 * |Q u|) :=
    mul_nonneg (mul_nonneg (by norm_num only) (sq_nonneg _))
      (intervalIntegral.integral_nonneg hy (fun _ _ ↦ mul_nonneg (sq_nonneg _) (abs_nonneg _)))
  have hedge : |4 * edge * gaussianLogZetaRemainder X| ≤ 5 / 3 * |edge| * c ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 4)]
    refine
      (mul_le_mul_of_nonneg_left (gaussian_log_remainder_large hX)
            (mul_nonneg (by norm_num only) (abs_nonneg _))).trans_eq
        ?_
    dsimp only [c]
    ring
  have hlo :=
    intervalIntegral.integral_add (hG.mono_set hsub₀) (hq₀.continuousOn_mul hlin.continuousOn)
  simp only [← add_mul, ← add_sub_assoc, G] at hlo
  have hAdd' := congrArg (fun v : ℝ ↦ (5 / 12 : ℝ) * c ^ 2 * v) hAdd
  unfold principalErrorFunctional
  change |3 * (∫ u in (0 : ℝ)..1, G u * Q u) - _ - _ + _| ≤ _
  rw [← hsplit]
  exact
    abs_le.mpr
      ⟨by linarith only [hlo, hlow.1, hhigh.1, htop.2, (abs_le.mp hedge).2, hAdd', hnn], by
        linarith only [hlo, hlow.2, hhigh.2, htop.1, (abs_le.mp hedge).1, hAdd', hnn]⟩

/-- Express the joint remainder bound in the polynomial coordinate. The low
part is an exponential tail and the high part is a finite exponential moment. -/
public theorem middle_principal_log_moments (B : Polynomial ℝ) (hRH : RiemannHypothesis) {d b X : ℝ}
    (hd : 0 < d) (hb : 0 < b) (hX : 1 ≤ X) :
    let D :=
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative
    let V := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    let F := fun u ↦ u * deriv V u
    let Q := deriv F
    |principalErrorFunctional Q gaussianLogZetaRemainder (F 1) X (Real.exp b) +
          3 * (∫ u in (0 : ℝ)..X⁻¹, (X * u - gaussianLogZetaConstant) * Q u)| ≤
      693 / 5000 *
          (Real.sqrt X *
            ∫ t in Set.Ioi (Real.log X), Real.exp (-(d + 1 / 2) * t) * |D.eval (b + t)|) +
        5 / 4 * X⁻¹ ^ 2 * Real.exp ((d - 2) * b) *
          (∫ t in (0 : ℝ)..(b + Real.log X), Real.exp (-(d - 2) * t) * |D.eval t|) +
        5 / 3 * |F 1| * X⁻¹ ^ 2 := by
  intro D V F Q
  have hp := zero_lt_one.trans_le hX
  have hy := Real.one_le_exp hb.le
  have hcut := ((inv_le_one₀ hp).mpr hX).trans hy
  have hq (u : ℝ) (hu : 0 < u) : |Q u| = u ^ (d - 1) * |D.eval (b - Real.log u)| := by
    change |deriv F u| = _
    rw [show deriv F u = _ from (reflected_log_weight_second B d b hu).deriv, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hu.le _)]
  have h₁ :
    (∫ u in (0 : ℝ)..X⁻¹, Real.sqrt (X * u) * |Q u|) =
      Real.sqrt X * ∫ t in Set.Ioi (Real.log X), Real.exp (-(d + 1 / 2) * t) * |D.eval (b + t)| :=
    (intervalIntegral.integral_congr_Ioo_of_le (inv_pos.mpr hp).le
          (fun u hu ↦ congrArg (Real.sqrt (X * u) * ·) (hq u hu.1))).trans
      (middle_low_sqrt_moment D d b hp)
  have h₂ :
    (∫ u in X⁻¹..Real.exp b, u⁻¹ ^ 2 * |Q u|) =
      Real.exp ((d - 2) * b) *
        ∫ t in (0 : ℝ)..(b + Real.log X), Real.exp (-(d - 2) * t) * |D.eval t| :=
    (intervalIntegral.integral_congr_Ioo_of_le hcut
          (fun u hu ↦ congrArg (u⁻¹ ^ 2 * ·) (hq u ((inv_pos.mpr hp).trans hu.1)))).trans
      (reflected_high_abs_moment D d b hp hcut)
  have hi := reflected_principal_integrable B hd hb
  have h := middle_principal_decay Q hRH (edge := F 1) hX hy hi.1 hi.2
  dsimp only at h
  rw [h₁, h₂] at h
  simpa only [mul_assoc] using h

/-- A directed bound at the left cutoff controls the physical lower charge on
an entire cutoff interval. The exponential factor uses the right cutoff. -/
public theorem middle_low_charge_on (D : Polynomial ℝ) {s b x l r κ A C : ℝ} (hs : 0 < s)
    (hl : 0 ≤ b + l) (hlx : l ≤ x) (hxr : x ≤ r) (hκ : 0 ≤ κ)
    (hA : (∫ t in Set.Ioi (b + l), Real.exp (-s * t) * |D.eval t|) ≤ A)
    (hC : 693 / 5000 * κ * Real.exp (r / 2) * A ≤ C) :
    693 / 5000 * κ * Real.exp (-s * b) * Real.exp (x / 2) *
        (∫ t in Set.Ioi x, Real.exp (-s * t) * |D.eval (b + t)|) ≤
      C := by
  let f := fun t ↦ Real.exp (-s * t) * |D.eval t|
  have ht :
    (∫ t in Set.Ioi (b + x), f t) =
      Real.exp (-s * b) * ∫ t in Set.Ioi x, Real.exp (-s * t) * |D.eval (b + t)| := by
    have hpre : (fun t : ℝ ↦ b + t) ⁻¹' Set.Ioi (b + x) = Set.Ioi x := by
      ext t
      exact add_lt_add_iff_left b
    have hemb : MeasurableEmbedding (fun t : ℝ ↦ b + t) :=
      (Homeomorph.addLeft b).isClosedEmbedding.measurableEmbedding
    have hm := MeasureTheory.measurePreserving_add_left MeasureTheory.volume b
    have htrans := hm.setIntegral_preimage_emb hemb f (Set.Ioi (b + x))
    rw [hpre] at htrans
    rw [← htrans]
    have he (t : ℝ) : f (b + t) = Real.exp (-s * b) * (Real.exp (-s * t) * |D.eval (b + t)|) := by
      simp only [f, mul_add, Real.exp_add, mul_assoc]
    simp only [he, MeasureTheory.integral_const_mul]
  have hmono := abs_laplace_tail_mono D hs hl (add_le_add (le_refl b) hlx)
  have hκ' : 0 ≤ (693 / 5000 : ℝ) * κ := mul_nonneg (by norm_num only) hκ
  have hex := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hxr (by norm_num only : 0 ≤ (2 : ℝ)))
  have hbound :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul hex (hmono.trans hA)
        (MeasureTheory.integral_nonneg (fun _ ↦ mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)))
        (Real.exp_nonneg _))
      hκ'
  change (693 / 5000 : ℝ) * κ * (Real.exp (x / 2) * (∫ t in Set.Ioi (b + x), f t)) ≤ _ at hbound
  rw [ht] at hbound
  refine le_trans ?_ (hbound.trans (by simpa only [mul_assoc] using hC))
  apply le_of_eq
  ring

/-- In the physical scale the factor from the square-root-weighted moment
cancels the normalization of the profile. A single left-endpoint absolute
moment therefore controls the lower error over the whole remaining ray. -/
public theorem middle_low_physical_charge (D : Polynomial ℝ) {s b x l κ A C : ℝ} (hs : 0 < s)
    (hl : 0 ≤ b + l) (hlx : l ≤ x) (hκ : 0 ≤ κ)
    (hA : (∫ t in Set.Ioi (b + l), Real.exp (-s * t) * |D.eval t|) ≤ A)
    (hC : 693 / 5000 * κ * A ≤ C) :
    693 / 5000 * (κ * Real.exp (-s * (x + b)) * Real.exp ((s - 1 / 2) * x)) * Real.exp (x / 2) *
        (∫ t in Set.Ioi x, Real.exp (-s * t) * |D.eval (b + t)|) ≤
      C := by
  have he := Real.exp_pos (x / 2)
  have hκ' : 0 ≤ (693 / 5000 : ℝ) * κ := mul_nonneg (by norm_num only) hκ
  have hh : 693 / 5000 * κ * Real.exp (x / 2) * A ≤ C * Real.exp (x / 2) := by
    calc
      _ = (693 / 5000 * κ * A) * Real.exp (x / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC he.le
  have h := middle_low_charge_on D hs hl hlx (le_refl x) hκ hA hh
  have h' :=
    le_of_mul_le_mul_right
      (show
        (693 / 5000 * κ * Real.exp (-s * b) *
              (∫ t in Set.Ioi x, Real.exp (-s * t) * |D.eval (b + t)|)) *
            Real.exp (x / 2) ≤
          C * Real.exp (x / 2)
        by
        convert h using 1
        ring)
      he
  have hf :
    Real.exp (-s * (x + b)) * Real.exp ((s - 1 / 2) * x) * Real.exp (x / 2) =
      Real.exp (-s * b) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ =
        693 / 5000 * κ * (Real.exp (-s * (x + b)) * Real.exp ((s - 1 / 2) * x) * Real.exp (x / 2)) *
          (∫ t in Set.Ioi x, Real.exp (-s * t) * |D.eval (b + t)|) :=
      by ring
    _ ≤ C := by
      rw [hf]; exact h'

/-- Bound the finite inverse-square remainder in physical coordinates on
an entire cutoff interval using one absolute integral at the largest support. -/
public theorem middle_upper_physical_charge (D : Polynomial ℝ) {s b x l r κ A C : ℝ}
    (hl : 0 ≤ b + l) (hlx : l ≤ x) (hxr : x ≤ r) (hκ : 0 ≤ κ)
    (hA : (∫ t in (0 : ℝ)..(b + r), Real.exp ((5 / 2 - s) * t) * |D.eval t|) ≤ A)
    (hC : 5 / 4 * κ * Real.exp (-(5 / 2 : ℝ) * (b + l)) * A ≤ C) :
    5 / 4 * (κ * Real.exp (-s * (x + b)) * Real.exp ((s - 1 / 2) * x)) * Real.exp (-2 * x) *
        Real.exp ((s - 5 / 2) * b) *
        (∫ t in (0 : ℝ)..(b + x), Real.exp ((5 / 2 - s) * t) * |D.eval t|) ≤
      C := by
  let f := fun t ↦ Real.exp ((5 / 2 - s) * t) * |D.eval t|
  have hf : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul D.continuous.abs
  have hfn (t : ℝ) : 0 ≤ f t := mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
  have hx : 0 ≤ b + x := hl.trans (add_le_add (le_refl b) hlx)
  have hxy : b + x ≤ b + r := add_le_add (le_refl b) hxr
  have hM :=
    intervalIntegral.integral_mono_interval le_rfl hx hxy (Filter.Eventually.of_forall hfn)
      (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 (b + r))
  have hE : Real.exp (-(5 / 2 : ℝ) * (b + x)) ≤ Real.exp (-(5 / 2 : ℝ) * (b + l)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (add_le_add (le_refl b) hlx) (by norm_num only))
  have he :
    Real.exp (-s * (x + b)) * Real.exp ((s - 1 / 2) * x) * Real.exp (-2 * x) *
        Real.exp ((s - 5 / 2) * b) =
      Real.exp (-(5 / 2 : ℝ) * (b + x)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hK : 0 ≤ (5 / 4 : ℝ) * κ := mul_nonneg (by norm_num only) hκ
  calc
    _ = 5 / 4 * κ * (Real.exp (-(5 / 2 : ℝ) * (b + x)) * (∫ t in 0..(b + x), f t)) := by
      rw [← he]
      dsimp only [f]
      ring
    _ ≤ _ :=
      (mul_le_mul_of_nonneg_left
            (mul_le_mul hE (hM.trans hA) (intervalIntegral.integral_nonneg hx (fun t _ ↦ hfn t))
              (Real.exp_nonneg _))
            hK).trans
        (by simpa only [mul_assoc] using hC)

/-- Combine the two checked physical moment charges with the explicit cutoff
boundary charge for the nonspectral remainder. -/
public theorem middle_physical_remainder_le (B : Polynomial ℝ) (hRH : RiemannHypothesis)
    {κ s b x L U : ℝ} (hκ : 0 ≤ κ) (hs : 1 / 2 < s) (hb : 0 < b) (hx : 0 ≤ x) :
    let X := Real.exp x
    let d := s - 1 / 2
    let c := κ * Real.exp (-s * (x + b)) * Real.exp (d * x)
    let D :=
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative
    let V := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    let F := fun u ↦ u * deriv V u
    (693 / 5000 * c * Real.exp (x / 2) * (∫ t in Set.Ioi x, Real.exp (-s * t) * |D.eval (b + t)|) ≤
        L) →
      (5 / 4 * c * Real.exp (-2 * x) * Real.exp ((s - 5 / 2) * b) *
          (∫ t in (0 : ℝ)..(b + x), Real.exp ((5 / 2 - s) * t) * |D.eval t|) ≤
        U) →
      c *
          |principalErrorFunctional (deriv F) gaussianLogZetaRemainder (F 1) X (Real.exp b) +
              3 * (∫ u in (0 : ℝ)..X⁻¹, (X * u - gaussianLogZetaConstant) * deriv F u)| ≤
        L + U + (5 / 3 * c * |F 1| * Real.exp (-2 * x)) := by
  intro X d c D V F hl hu
  have hp : 0 < X := Real.exp_pos _
  have hX : 1 ≤ X := Real.one_le_exp hx
  have hd : 0 < d := sub_pos.mpr hs
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg hκ (Real.exp_nonneg _)) (Real.exp_nonneg _)
  have hlog : Real.log X = x := Real.log_exp _
  have hroot : Real.sqrt X = Real.exp (x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp, hlog, div_eq_mul_inv]
    congr 1
    ring
  have hsq : X⁻¹ ^ (2 : ℕ) = Real.exp (-2 * x) := by
    dsimp only [X]
    rw [← Real.exp_neg, pow_two, ← Real.exp_add]
    congr 1
    ring
  have h := middle_principal_log_moments B hRH hd hb hX
  dsimp only at h
  rw [hlog, hroot, hsq] at h
  have hs' : d + 1 / 2 = s := sub_add_cancel _ _
  have hd' : d - 2 = s - 5 / 2 := by
    dsimp only [d]; ring
  rw [hs', hd', show -(s - 5 / 2) = 5 / 2 - s by ring] at h
  have hm := mul_le_mul_of_nonneg_left h hc
  calc
    _ ≤
        c *
          (693 / 5000 *
              (Real.exp (x / 2) * ∫ t in Set.Ioi x, Real.exp (-s * t) * |D.eval (b + t)|) +
            5 / 4 * Real.exp (-2 * x) * Real.exp ((s - 5 / 2) * b) *
              (∫ t in (0 : ℝ)..(b + x), Real.exp ((5 / 2 - s) * t) * |D.eval t|) +
            5 / 3 * |F 1| * Real.exp (-2 * x)) :=
      hm
    _ ≤ _ := by linarith only [hl, hu]

/-- The cutoff boundary of a reflected profile is its value times the power
rate minus the derivative, evaluated at the shift. -/
public theorem reflected_log_edge_eval (B : Polynomial ℝ) (d b : ℝ) :
    let V := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    (fun u ↦ u * deriv V u) 1 = d * B.eval b - B.derivative.eval b := by
  intro V
  change 1 * deriv V 1 = _
  rw [(reflected_log_weight_deriv B d b zero_lt_one).deriv]
  simp only [Real.log_one, sub_zero, Real.one_rpow, one_mul, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C]

end PseudoPrime.PrimeTestBounds.MillerRabin
