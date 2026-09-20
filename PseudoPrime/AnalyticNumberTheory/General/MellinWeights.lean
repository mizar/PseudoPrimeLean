/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Mellin transforms of two elementary smoothing weights

This file computes the Mellin transform of two elementary smoothing weights on `(0, ∞)`:
the reciprocal weight `w₁(t) = 1_{(0,1]}(t)(1 - t)`, and the logarithmic
weight `w₂(t) = 1_{(0,1]}(t)(-log t)`.  Both computations reduce to the existing
mathlib Mellin transform API (`hasMellin_one_Ioc`, `hasMellin_cpow_Ioc`,
`mellin_hasDerivAt_of_isBigO_rpow`); no general Perron theory is built here.
These weights and their rational Mellin kernels `1 / (s(s+1))` and `1 / s²` are the standard
ingredients used to convert Dirichlet-series identities into finite-sum explicit formulae via
Mellin inversion; the material here is independent of any specific contour or Dirichlet series.
-/

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The reciprocal smoothing weight `1_{(0,1]}(t)(1 - t)`. -/
noncomputable def mellinWeightOne : ℝ → ℂ :=
  Set.indicator (Set.Ioc (0 : ℝ) 1) (fun t ↦ 1 - (t : ℂ))

/-- The reciprocal weight is the difference of the two indicator pieces `1` and `t ↦ t`. -/
theorem mellinWeightOne_eq_sub :
    mellinWeightOne = fun t ↦
      Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ ↦ (1 : ℂ)) t -
        Set.indicator (Set.Ioc (0 : ℝ) 1) (fun t ↦ (t : ℂ) ^ (1 : ℂ)) t := by
  funext t
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
  · simp only [mellinWeightOne, Set.indicator_of_mem ht, Complex.cpow_one]
  · simp only [mellinWeightOne, Set.indicator_of_notMem ht, Complex.cpow_one, sub_self]

/-- The Mellin transform of the reciprocal weight is the rational kernel `1 / (s(s+1))`. -/
theorem hasMellin_mellinWeightOne {s : ℂ} (hs : 0 < s.re) :
    HasMellin mellinWeightOne s (1 / (s * (s + 1))) := by
  have h1 := hasMellin_one_Ioc hs
  have h2 :=
    hasMellin_cpow_Ioc (1 : ℂ)
      (show (0 : ℝ) < s.re + (1 : ℂ).re by
        simp only [Complex.one_re]; linarith)
  have hsub := hasMellin_sub h1.1 h2.1
  rw [h1.2, h2.2] at hsub
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp only [Complex.zero_re, lt_self_iff_false] at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre : s.re + 1 = 0 := by
      simpa only [Complex.add_re, Complex.one_re, Complex.zero_re] using congrArg Complex.re h
    linarith
  have hval : (1 : ℂ) / s - 1 / (s + 1) = 1 / (s * (s + 1)) := by
    field_simp
    ring
  rw [hval] at hsub
  rwa [mellinWeightOne_eq_sub]

/-- The base indicator weight `1_{(0,1]}`, whose Mellin derivative produces the logarithmic
weight. -/
noncomputable def mellinWeightZero : ℝ → ℂ :=
  Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ ↦ 1)

/-- The logarithmic smoothing weight `1_{(0,1]}(t)(-log t)`. -/
noncomputable def mellinWeightTwo : ℝ → ℂ :=
  Set.indicator (Set.Ioc (0 : ℝ) 1) (fun t ↦ -(Real.log t : ℂ))

/-- The logarithmic weight is minus the real-log-scaled base indicator weight. -/
theorem mellinWeightTwo_eq_neg_smul_log :
    mellinWeightTwo = fun t ↦ -(Real.log t • mellinWeightZero t) := by
  funext t
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
  · simp only [mellinWeightTwo, Set.indicator_of_mem ht, mellinWeightZero, Complex.real_smul,
      mul_one]
  · simp only [mellinWeightTwo, Set.indicator_of_notMem ht, mellinWeightZero, smul_zero, neg_zero]

/-- The base weight is locally integrable on the positive reals. -/
theorem locallyIntegrableOn_mellinWeightZero :
    MeasureTheory.LocallyIntegrableOn mellinWeightZero (Set.Ioi 0) := by
  exact
    ((MeasureTheory.locallyIntegrable_const (1 : ℂ)).indicator
          measurableSet_Ioc).locallyIntegrableOn
      _

/-- The base weight vanishes eventually at infinity, so it is `O` of any negative power. -/
theorem isBigO_atTop_mellinWeightZero (a : ℝ) :
    mellinWeightZero =O[Filter.atTop] (fun t : ℝ ↦ t ^ (-a)) := by
  have hzero : mellinWeightZero =ᶠ[Filter.atTop] 0 := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with t ht
    simp only [mellinWeightZero, Pi.zero_apply]
    rw [Set.indicator_of_notMem]
    intro h
    linarith only [h.2, ht]
  exact hzero.trans_isBigO (Asymptotics.isBigO_zero _ _)

/-- The base weight is eventually the constant `1` just to the right of zero. -/
theorem isBigO_nhdsWithin_mellinWeightZero :
    mellinWeightZero =O[nhdsWithin 0 (Set.Ioi 0)] (fun t : ℝ ↦ t ^ (-(0 : ℝ))) := by
  have hone : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), mellinWeightZero t = 1 := by
    filter_upwards [Ioo_mem_nhdsGT (one_pos)] with t ht
    have hmem : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    exact Set.indicator_of_mem hmem _
  apply Asymptotics.IsBigO.of_bound'
  filter_upwards [hone] with t ht
  simp only [ht, norm_one, neg_zero, Real.rpow_zero, Std.le_refl]

/-- The Mellin transform of the base weight matches its known closed form near `s`. -/
theorem eventually_mellin_mellinWeightZero_eq {s : ℂ} (hs : 0 < s.re) :
    ∀ᶠ z in nhds s, mellin mellinWeightZero z = z⁻¹ := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with z hz
  have := (hasMellin_one_Ioc hz).2
  simpa only [mellinWeightZero, one_div] using this

/-- The Mellin transform of the logarithmic weight is the rational kernel `1 / s²`. -/
theorem hasMellin_mellinWeightTwo {s : ℂ} (hs : 0 < s.re) :
    HasMellin mellinWeightTwo s (1 / s ^ 2) := by
  obtain ⟨hconv, hderiv⟩ :=
    mellin_hasDerivAt_of_isBigO_rpow locallyIntegrableOn_mellinWeightZero
      (isBigO_atTop_mellinWeightZero (s.re + 1)) (by linarith) isBigO_nhdsWithin_mellinWeightZero hs
  have hinv : HasDerivAt (fun z : ℂ ↦ z⁻¹) (-(s ^ 2)⁻¹) s :=
    hasDerivAt_inv
      (by
        intro h
        rw [h] at hs
        simp only [Complex.zero_re, lt_self_iff_false] at hs)
  have hderiv' : HasDerivAt (mellin mellinWeightZero) (-(s ^ 2)⁻¹) s :=
    hinv.congr_of_eventuallyEq (eventually_mellin_mellinWeightZero_eq hs)
  have hval : mellin (fun t : ℝ ↦ Real.log t • mellinWeightZero t) s = -(s ^ 2)⁻¹ :=
    hderiv.unique hderiv'
  have hpoint :
    (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • mellinWeightTwo t) = fun t : ℝ ↦
      -((t : ℂ) ^ (s - 1) • (Real.log t • mellinWeightZero t)) := by
    rw [mellinWeightTwo_eq_neg_smul_log]
    funext t
    rw [smul_neg]
  have hconv' : MellinConvergent mellinWeightTwo s := by
    unfold MellinConvergent
    rw [hpoint]
    exact hconv.neg
  refine ⟨hconv', ?_⟩
  have hmellin_eq :
    mellin mellinWeightTwo s = -mellin (fun t : ℝ ↦ Real.log t • mellinWeightZero t) s := by
    unfold mellin
    rw [hpoint, MeasureTheory.integral_neg]
  rw [hmellin_eq, hval]
  field_simp

/-- A vertical line's imaginary displacement never returns to `0` once the real part is nonzero. -/
theorem ne_zero_add_mul_I_of_re_ne_zero {σ : ℝ} (hσ0 : σ ≠ 0) (y : ℝ) :
    (σ : ℂ) + y * Complex.I ≠ 0 := by
  intro h
  exact
    hσ0
      (by
        simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.zero_re] using
          congrArg Complex.re h)

/-- The squared norm of a point on a vertical line at `σ`. -/
theorem norm_add_mul_I_sq (σ y : ℝ) : ‖(σ : ℂ) + y * Complex.I‖ ^ 2 = σ ^ 2 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]

/-- The squared modulus on a vertical line at `σ` dominates a shifted parabola in `y`. -/
theorem min_sq_one_mul_le_norm_add_mul_I_sq (σ y : ℝ) :
    min (σ ^ 2) 1 * (1 + y ^ 2) ≤ ‖(σ : ℂ) + y * Complex.I‖ ^ 2 := by
  rw [norm_add_mul_I_sq, mul_add, mul_one]
  have h1 : min (σ ^ 2) 1 ≤ σ ^ 2 := min_le_left _ _
  have h2 : min (σ ^ 2) 1 * y ^ 2 ≤ y ^ 2 := mul_le_of_le_one_left (sq_nonneg y) (min_le_right _ _)
  linarith

/-- The logarithmic rational kernel `s ↦ s⁻² ` is vertically integrable off the imaginary axis. -/
theorem verticalIntegrable_mellinLogKernel {σ : ℝ} (hσ0 : σ ≠ 0) :
    Complex.VerticalIntegrable (fun s : ℂ ↦ (s : ℂ)⁻¹ ^ 2) σ := by
  unfold Complex.VerticalIntegrable
  have hc : (0 : ℝ) < min (σ ^ 2) 1 := lt_min (by positivity) one_pos
  apply MeasureTheory.Integrable.mono' (integrable_inv_one_add_sq.const_mul (min (σ ^ 2) 1)⁻¹)
  · fun_prop (disch := exact ne_zero_add_mul_I_of_re_ne_zero hσ0 _)
  · filter_upwards with y
    have hnorm : ‖((σ : ℂ) + y * Complex.I)⁻¹ ^ 2‖ = (‖(σ : ℂ) + y * Complex.I‖ ^ 2)⁻¹ := by
      rw [norm_pow, norm_inv, inv_pow]
    rw [hnorm, ← mul_inv, ← one_div, ← one_div]
    have hb := min_sq_one_mul_le_norm_add_mul_I_sq σ y
    have hcy : 0 < min (σ ^ 2) 1 * (1 + y ^ 2) := mul_pos hc (by positivity)
    exact one_div_le_one_div_of_le hcy hb

/-- The reciprocal rational kernel `s ↦ (s(s+1))⁻¹` is vertically integrable off `σ = 0, -1`. -/
theorem verticalIntegrable_mellinReciprocalKernel {σ : ℝ} (hσ0 : σ ≠ 0) (hσ1 : σ ≠ -1) :
    Complex.VerticalIntegrable (fun s : ℂ ↦ (s * (s + 1))⁻¹) σ := by
  unfold Complex.VerticalIntegrable
  have hσ1' : σ + 1 ≠ 0 := by
    intro h
    apply hσ1
    linarith
  have hc1 : (0 : ℝ) < min (σ ^ 2) 1 := lt_min (by positivity) one_pos
  have hc2 : (0 : ℝ) < min ((σ + 1) ^ 2) 1 := lt_min (by positivity) one_pos
  set c : ℝ := Real.sqrt (min (σ ^ 2) 1 * min ((σ + 1) ^ 2) 1) with hc_def
  have hc : 0 < c := Real.sqrt_pos.mpr (mul_pos hc1 hc2)
  have hne (y : ℝ) : (σ : ℂ) + y * Complex.I ≠ 0 ∧ (σ : ℂ) + y * Complex.I + 1 ≠ 0 := by
    refine ⟨ne_zero_add_mul_I_of_re_ne_zero hσ0 y, ?_⟩
    have : (σ : ℂ) + y * Complex.I + 1 = ((σ + 1 : ℝ) : ℂ) + y * Complex.I := by
      push_cast; ring
    rw [this]
    exact ne_zero_add_mul_I_of_re_ne_zero hσ1' y
  apply MeasureTheory.Integrable.mono' (integrable_inv_one_add_sq.const_mul c⁻¹)
  · apply Measurable.aestronglyMeasurable
    fun_prop (disch :=
      first
      | exact mul_ne_zero (hne _).1 (hne _).2
      | exact (hne _).1
      | exact (hne _).2)
  · filter_upwards with y
    set s : ℂ := (σ : ℂ) + y * Complex.I with hs_def
    have hs1 : s + 1 = ((σ + 1 : ℝ) : ℂ) + y * Complex.I := by
      rw [hs_def]; push_cast; ring
    have hnorm : ‖(s * (s + 1))⁻¹‖ = (‖s‖ * ‖s + 1‖)⁻¹ := by rw [norm_inv, norm_mul]
    have e1 := min_sq_one_mul_le_norm_add_mul_I_sq σ y
    have e2 := min_sq_one_mul_le_norm_add_mul_I_sq (σ + 1) y
    rw [← hs_def] at e1
    rw [← hs1] at e2
    have hsq : min (σ ^ 2) 1 * min ((σ + 1) ^ 2) 1 * (1 + y ^ 2) ^ 2 ≤ (‖s‖ * ‖s + 1‖) ^ 2 := by
      calc
        min (σ ^ 2) 1 * min ((σ + 1) ^ 2) 1 * (1 + y ^ 2) ^ 2 =
            (min (σ ^ 2) 1 * (1 + y ^ 2)) * (min ((σ + 1) ^ 2) 1 * (1 + y ^ 2)) :=
          by ring
        _ ≤ ‖s‖ ^ 2 * ‖s + 1‖ ^ 2 := mul_le_mul e1 e2 (by positivity) (by positivity)
        _ = (‖s‖ * ‖s + 1‖) ^ 2 := by ring
    have hprod : c * (1 + y ^ 2) ≤ ‖s‖ * ‖s + 1‖ := by
      have h := Real.sqrt_le_sqrt hsq
      rwa [show min (σ ^ 2) 1 * min ((σ + 1) ^ 2) 1 * (1 + y ^ 2) ^ 2 = (c * (1 + y ^ 2)) ^ 2 by
          rw [mul_pow, hc_def, Real.sq_sqrt (mul_nonneg hc1.le hc2.le)],
        Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at h
    rw [hnorm, ← mul_inv, ← one_div, ← one_div]
    have hcy : 0 < c * (1 + y ^ 2) := mul_pos hc (by positivity)
    exact one_div_le_one_div_of_le hcy hprod

/-- On the positive reals, the reciprocal weight is the shifted-clamped linear function. -/
theorem mellinWeightOne_eq_ofReal_max {t : ℝ} (ht : 0 < t) :
    mellinWeightOne t = ((max (1 - t) 0 : ℝ) : ℂ) := by
  by_cases h : t ∈ Set.Ioc (0 : ℝ) 1
  · rw [mellinWeightOne, Set.indicator_of_mem h, max_eq_left (by linarith only [h.2])]
    push_cast
    ring
  · have h1 : 1 < t := by
      by_contra hc
      exact h ⟨ht, not_lt.mp hc⟩
    rw [mellinWeightOne, Set.indicator_of_notMem h, max_eq_right (by linarith)]
    simp only [Complex.ofReal_zero]

/-- The reciprocal weight is continuous at every positive real. -/
theorem continuousAt_mellinWeightOne {x : ℝ} (hx : 0 < x) : ContinuousAt mellinWeightOne x := by
  have heq : Set.EqOn mellinWeightOne (fun t ↦ ((max (1 - t) 0 : ℝ) : ℂ)) (Set.Ioi 0) := fun t ht ↦
    mellinWeightOne_eq_ofReal_max ht
  refine (ContinuousOn.congr ?_ heq).continuousAt (isOpen_Ioi.mem_nhds hx)
  fun_prop

/-- On the positive reals, the logarithmic weight is minus the log of the clamp at `1`. -/
theorem mellinWeightTwo_eq_ofReal_neg_log_min {t : ℝ} (ht : 0 < t) :
    mellinWeightTwo t = ((-Real.log (min t 1) : ℝ) : ℂ) := by
  by_cases h : t ∈ Set.Ioc (0 : ℝ) 1
  · rw [mellinWeightTwo, Set.indicator_of_mem h, min_eq_left h.2]
    push_cast
    ring
  · have h1 : 1 < t := by
      by_contra hc
      exact h ⟨ht, not_lt.mp hc⟩
    rw [mellinWeightTwo, Set.indicator_of_notMem h, min_eq_right h1.le, Real.log_one]
    simp only [neg_zero, Complex.ofReal_zero]

/-- The logarithmic weight is continuous at every positive real. -/
theorem continuousAt_mellinWeightTwo {x : ℝ} (hx : 0 < x) : ContinuousAt mellinWeightTwo x := by
  have heq : Set.EqOn mellinWeightTwo (fun t ↦ ((-Real.log (min t 1) : ℝ) : ℂ)) (Set.Ioi 0) :=
    fun t ht ↦ mellinWeightTwo_eq_ofReal_neg_log_min ht
  refine (ContinuousOn.congr ?_ heq).continuousAt (isOpen_Ioi.mem_nhds hx)
  intro t ht
  have hmin_cont : ContinuousAt (fun u : ℝ ↦ min u 1) t :=
    (continuous_id.min continuous_const).continuousAt
  have hminx_ne : min t 1 ≠ 0 := (lt_min ht one_pos).ne'
  have hlog_cont : ContinuousAt (fun u : ℝ ↦ Real.log (min u 1)) t := hmin_cont.log hminx_ne
  exact (Complex.continuous_ofReal.continuousAt.comp hlog_cont.neg).continuousWithinAt

/-- The Mellin inversion formula recovers the reciprocal weight from its rational kernel. -/
theorem mellinInv_mellinWeightOne_eq {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    mellinInv σ (fun s : ℂ ↦ 1 / (s * (s + 1))) x = mellinWeightOne x := by
  have hconv :=
    (hasMellin_mellinWeightOne (s := (σ : ℂ)) (by simpa only [Complex.ofReal_re] using hσ)).1
  have hpoint :
    ∀ y : ℝ,
      mellin mellinWeightOne ((σ : ℂ) + y * Complex.I) =
        1 / (((σ : ℂ) + y * Complex.I) * ((σ : ℂ) + y * Complex.I + 1)) :=
    fun y ↦
    (hasMellin_mellinWeightOne
        (show (0 : ℝ) < ((σ : ℂ) + (y : ℂ) * Complex.I).re by
          simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hσ)).2
  have hVI : Complex.VerticalIntegrable (mellin mellinWeightOne) σ := by
    have hEq :
      (fun y : ℝ ↦ mellin mellinWeightOne ((σ : ℂ) + y * Complex.I)) = fun y : ℝ ↦
        (((σ : ℂ) + y * Complex.I) * ((σ : ℂ) + y * Complex.I + 1))⁻¹ := by
      funext y; rw [hpoint y, one_div]
    unfold Complex.VerticalIntegrable
    rw [hEq]
    exact
      verticalIntegrable_mellinReciprocalKernel hσ.ne'
        (by
          intro h; rw [h] at hσ; linarith)
  have hmellinInv :=
    mellinInv_mellin_eq σ mellinWeightOne hx hconv hVI (continuousAt_mellinWeightOne hx)
  have hfun_eq :
    (fun y : ℝ ↦
        (x : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) •
          (1 / (((σ : ℂ) + y * Complex.I) * ((σ : ℂ) + y * Complex.I + 1)))) =
      fun y : ℝ ↦
      (x : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) •
        mellin mellinWeightOne ((σ : ℂ) + y * Complex.I) := by
    funext y; rw [hpoint y]
  rw [← hmellinInv]
  unfold mellinInv
  rw [hfun_eq]

/-- The Mellin inversion formula recovers the logarithmic weight from its rational kernel. -/
theorem mellinInv_mellinWeightTwo_eq {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    mellinInv σ (fun s : ℂ ↦ 1 / s ^ 2) x = mellinWeightTwo x := by
  have hconv :=
    (hasMellin_mellinWeightTwo (s := (σ : ℂ)) (by simpa only [Complex.ofReal_re] using hσ)).1
  have hpoint :
    ∀ y : ℝ, mellin mellinWeightTwo ((σ : ℂ) + y * Complex.I) = 1 / ((σ : ℂ) + y * Complex.I) ^ 2 :=
    fun y ↦
    (hasMellin_mellinWeightTwo
        (show (0 : ℝ) < ((σ : ℂ) + (y : ℂ) * Complex.I).re by
          simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hσ)).2
  have hVI : Complex.VerticalIntegrable (mellin mellinWeightTwo) σ := by
    have hEq :
      (fun y : ℝ ↦ mellin mellinWeightTwo ((σ : ℂ) + y * Complex.I)) = fun y : ℝ ↦
        (((σ : ℂ) + y * Complex.I)⁻¹) ^ 2 := by
      funext y; rw [hpoint y, one_div, inv_pow]
    unfold Complex.VerticalIntegrable
    rw [hEq]
    exact verticalIntegrable_mellinLogKernel hσ.ne'
  have hmellinInv :=
    mellinInv_mellin_eq σ mellinWeightTwo hx hconv hVI (continuousAt_mellinWeightTwo hx)
  have hfun_eq :
    (fun y : ℝ ↦ (x : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) • (1 / ((σ : ℂ) + y * Complex.I) ^ 2)) =
      fun y : ℝ ↦
      (x : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) •
        mellin mellinWeightTwo ((σ : ℂ) + y * Complex.I) := by
    funext y; rw [hpoint y]
  rw [← hmellinInv]
  unfold mellinInv
  rw [hfun_eq]

/-- For a nonnegative numerator and positive denominator, the complex power of their quotient
splits into the numerator power and the inverse denominator power. -/
theorem cpow_div_eq_cpow_mul_cpow_neg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (s : ℂ) :
    ((a / b : ℝ) : ℂ) ^ s = (a : ℂ) ^ s * (b : ℂ) ^ (-s) := by
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg ha hb.le, Complex.cpow_neg, div_eq_mul_inv]

end PseudoPrime.AnalyticNumberTheory.General
