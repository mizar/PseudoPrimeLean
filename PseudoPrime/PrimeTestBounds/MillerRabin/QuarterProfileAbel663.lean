/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfileWeight663
public import PseudoPrime.Analysis.LogPowerTailIntegral
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxAbel656
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbelInterval
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevBoundary43
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.EulerDerivatives

/-! # Signed Abel integral for the section 137 Euler profile -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed physical reflected density in (137.21). -/
@[expose]
noncomputable def quarterDensity663 (t : ℝ) : ℝ :=
  t ^ (-(8 / 5) : ℝ) * quarterProfile663 (Real.log t)

/-- The derivative polynomial σ F - F' in displacement from 23/2. -/
private noncomputable def profileSlope (x : ℝ) : ℝ :=
  ((8 / 5) * profileCoeff 0 - profileCoeff 1) +
    ((8 / 5) * profileCoeff 1 - 2 * profileCoeff 2) * x +
    (8 / 5) * profileCoeff 2 * x ^ 2

/-- Differentiate the physical density with its actual signed profile. -/
private theorem density_deriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt quarterDensity663 (-(t ^ (-(13 / 5) : ℝ)) * profileSlope (Real.log t - 23 / 2))
      t := by
  have hlog := (Real.hasDerivAt_log ht.ne').sub_const (23 / 2)
  have h :=
    (Real.hasDerivAt_rpow_const (p := -(8 / 5 : ℝ)) (Or.inl ht.ne')).mul
      (((hasDerivAt_const t (profileCoeff 0)).add (hlog.const_mul (profileCoeff 1))).add
        ((hlog.pow 2).const_mul (profileCoeff 2)))
  have hp : t ^ (-(13 / 5) : ℝ) = t ^ (-(8 / 5) : ℝ) / t := by
    rw [show -(13 / 5 : ℝ) = -(8 / 5) - 1 by norm_num only, Real.rpow_sub ht, Real.rpow_one]
  convert h using 1
  · funext v
    simp only [quarterDensity663, profile_expand, Pi.add_apply, Pi.pow_apply, Pi.mul_apply]
  · rw [show -(8 / 5 : ℝ) - 1 = -(13 / 5) by norm_num only, hp]
    simp only [profileSlope, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat]
    ring

/-- The main integrand is integrable on every tail above one. -/
private theorem density_integrable {x : ℝ} (hx : 1 ≤ x) :
    MeasureTheory.IntegrableOn quarterDensity663 (Set.Ioi x) := by
  apply
    (aux_integrable_quad (d := 3 / 5) (by norm_num only) hx 0 (profileCoeff 2) (profileCoeff 1)
        (profileCoeff 0) (23 / 2)).congr
  exact
    Filter.Eventually.of_forall fun t ↦ by
      simp only [quarterDensity663, profile_expand, pow_zero, mul_one,
        show -(3 / 5 : ℝ) - 1 = -(8 / 5) by norm_num only]
      ring

/-- The improper main integral retains the exact signed coefficients. -/
private theorem profile_main {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in Set.Ioi x, quarterDensity663 t) =
      x ^ (-(3 / 5) : ℝ) *
        (profileCoeff 2 * Analysis.logPowerTailPoly (3 / 5) 2 (Real.log x) +
          (profileCoeff 1 - 23 * profileCoeff 2) *
            Analysis.logPowerTailPoly (3 / 5) 1 (Real.log x) +
          (profileCoeff 0 - (23 / 2) * profileCoeff 1 + (23 / 2) ^ 2 * profileCoeff 2) *
            Analysis.logPowerTailPoly (3 / 5) 0 (Real.log x)) := by
  have h :=
    aux_integral_quad (d := 3 / 5) (by norm_num only) hx 0 (profileCoeff 2) (profileCoeff 1)
      (profileCoeff 0) (23 / 2)
  have he (t : ℝ) :
    t ^ (-(3 / 5 : ℝ) - 1) * Real.log t ^ 0 *
        (profileCoeff 2 * (Real.log t - 23 / 2) ^ 2 + profileCoeff 1 * (Real.log t - 23 / 2) +
          profileCoeff 0) =
      quarterDensity663 t := by
    simp only [quarterDensity663, profile_expand, pow_zero, mul_one,
      show -(3 / 5 : ℝ) - 1 = -(8 / 5) by norm_num only]
    ring
  simp only [he, Nat.zero_add] at h
  convert h using 1
  ring

/-- The Mangoldt-weighted signed series is absolutely convergent. -/
theorem quarter_profile_summable_663 :
    Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterDensity663 n) := by
  have hm :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 8 / 5)
      (by norm_num only)
  let A := profileCoeff 2
  let B := profileCoeff 1
  let C := profileCoeff 0
  let T : ℝ := 23 / 2
  apply
    (((hm 2).mul_left A).add ((hm 1).mul_left (B - 2 * A * T))).add
        ((hm 0).mul_left (C - B * T + A * T ^ 2)) |>.congr
  intro n
  simp only [quarterDensity663, profile_expand, Real.rpow_neg (Nat.cast_nonneg n), pow_zero,
    pow_one, A, B, C, T, div_eq_mul_inv]
  ring

/-- The centered boundary vanishes by power decay of the three moments. -/
private theorem density_boundary :
    Filter.Tendsto (fun t : ℝ ↦ (Chebyshev.psi t - t) * quarterDensity663 t) Filter.atTop
      (nhds 0) := by
  let E := fun t : ℝ ↦ (Chebyshev.psi t - t) / 4
  have hE : ∀ᶠ t : ℝ in Filter.atTop, ‖E t‖ ≤ 2 * t := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    have h₀ := zero_le_one.trans ht
    have hlog := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 4)
    have hψ :=
      (Chebyshev.psi_le_const_mul_self h₀).trans
        (mul_le_mul_of_nonneg_right (by linarith only [hlog] : Real.log 4 + 4 ≤ 7) h₀)
    rw [Real.norm_eq_abs, abs_le]
    dsimp only [E]
    exact ⟨by linarith only [Chebyshev.psi_nonneg (x := t), h₀], by linarith only [hψ, h₀]⟩
  have hm (k : ℕ) :=
    AnalyticNumberTheory.RiemannZeta.moment_boundary_tendsto (by norm_num only : (1 : ℝ) < 8 / 5) k
      E hE
  let A := profileCoeff 2
  let B := profileCoeff 1
  let C := profileCoeff 0
  let T : ℝ := 23 / 2
  have h :=
    (((hm 2).const_mul (4 * A)).add ((hm 1).const_mul (4 * (B - 2 * A * T)))).add
      ((hm 0).const_mul (4 * (C - B * T + A * T ^ 2)))
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  exact
    Filter.Eventually.of_forall
      (fun t ↦ by
        simp only [E, A, B, C, T, quarterDensity663, profile_expand,
          AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight, pow_zero, pow_one]
        ring)

/-- A nonnegative-coefficient upper bound on the absolute signed slope. -/
private theorem slope_abs {x : ℝ} (hx : 0 ≤ x) : |profileSlope x| ≤ 11 + 16 * x + 6 * x ^ 2 := by
  have hb := profile_coeff_bounds
  have h₀ : |(8 / 5 : ℝ) * profileCoeff 0 - profileCoeff 1| ≤ 11 :=
    abs_le.mpr ⟨by linarith only [hb.1.1, hb.2.1.2], by linarith only [hb.1.2, hb.2.1.1]⟩
  have h₁ : |(8 / 5 : ℝ) * profileCoeff 1 - 2 * profileCoeff 2| ≤ 16 :=
    abs_le.mpr ⟨by linarith only [hb.2.1.1, hb.2.2.2], by linarith only [hb.2.1.2, hb.2.2.1]⟩
  have h₂ : |(8 / 5 : ℝ) * profileCoeff 2| ≤ 6 :=
    abs_le.mpr ⟨by linarith only [hb.2.2.1], by linarith only [hb.2.2.2]⟩
  unfold profileSlope
  apply (abs_add_le _ _).trans
  rw [abs_mul ((8 / 5 : ℝ) * profileCoeff 2), abs_of_nonneg (sq_nonneg x)]
  apply add_le_add _ (mul_le_mul_of_nonneg_right h₂ (sq_nonneg x))
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg hx]
  exact add_le_add h₀ (mul_le_mul_of_nonneg_right h₁ hx)

/-- At a cutoff above one, the signed Mangoldt tail equals its main
integral minus the two centered corrections. -/
theorem quarter_profile_abel_663 {x : ℝ} (hx : 1 ≤ x)
    (he :
      MeasureTheory.IntegrableOn (fun t ↦ (Chebyshev.psi t - t) * deriv quarterDensity663 t)
        (Set.Ioi x)) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterDensity663 n) -
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * quarterDensity663 n =
      (∫ t in Set.Ioi x, quarterDensity663 t) - (Chebyshev.psi x - x) * quarterDensity663 x -
        ∫ t in Set.Ioi x, (Chebyshev.psi t - t) * deriv quarterDensity663 t := by
  have hd (t : ℝ) (ht : 1 ≤ t) := density_deriv (zero_lt_one.trans_le ht)
  apply
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_integral (zero_le_one.trans hx)
      (fun _ _ t ht ↦ (hd t (hx.trans ht.1)).differentiableAt) _ (density_integrable hx) he
      density_boundary quarter_profile_summable_663
  intro y _
  refine
    ContinuousOn.integrableOn_Icc (ContinuousOn.congr ?_ fun t ht ↦ (hd t (hx.trans ht.1)).deriv)
  intro t ht
  have ht₀ := (zero_lt_one.trans_le (hx.trans ht.1)).ne'
  have hl := Real.continuousAt_log ht₀
  have hpow := Real.continuousAt_rpow_const t (-(13 / 5 : ℝ)) (Or.inl ht₀)
  have hs : ContinuousAt (fun v ↦ profileSlope (Real.log v - 23 / 2)) t := by
    unfold profileSlope
    fun_prop
  exact (hpow.neg.mul hs).continuousWithinAt

/-- The low Chebyshev majorant for the centered error. -/
private noncomputable def finiteMajor (t : ℝ) : ℝ :=
  (4 / 5) *
    (t ^ (-(21 / 10) : ℝ) * (11 + 16 * (Real.log t - 23 / 2) + 6 * (Real.log t - 23 / 2) ^ 2))

/-- The log-square RH majorant for the centered error. -/
private noncomputable def highMajor (t : ℝ) : ℝ :=
  (1 / 24) *
    (t ^ (-(21 / 10) : ℝ) * Real.log t ^ 2 *
      (11 + 16 * (Real.log t - 23 / 2) + 6 * (Real.log t - 23 / 2) ^ 2))

/-- The two moments majorize the centered error on their respective
ranges. The low majorant may also be retained on the high range. -/
private theorem profile_error_major (hRH : RiemannHypothesis) {t : ℝ} (ht : 1423 ≤ t)
    (hl : 23 / 2 ≤ Real.log t) :
    ‖(Chebyshev.psi t - t) * deriv quarterDensity663 t‖ ≤
      finiteMajor t + (Set.Ioi (1000000 : ℝ)).indicator highMajor t := by
  have ht₀ : 0 < t := by linarith only [ht]
  have hlog := sub_nonneg.mpr hl
  have he : Real.sqrt t * t ^ (-(13 / 5) : ℝ) = t ^ (-(21 / 10) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht₀]
    norm_num only
  have hd := (density_deriv ht₀).deriv
  rw [hd, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg (Real.rpow_nonneg ht₀.le _)]
  have hS := mul_le_mul_of_nonneg_left (slope_abs hlog) (Real.rpow_nonneg ht₀.le (-(13 / 5)))
  have hS₀ :=
    mul_nonneg (Real.rpow_nonneg ht₀.le (-(13 / 5)))
      (abs_nonneg (profileSlope (Real.log t - 23 / 2)))
  by_cases h : t ≤ 1000000
  · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (1000000 : ℝ) from not_lt.mpr h), add_zero]
    have hψ := AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million ht h
    unfold finiteMajor
    linear_combination
      (mul_le_mul hψ hS hS₀ (by positivity)) +
        (4 / 5) * (11 + 16 * (Real.log t - 23 / 2) + 6 * (Real.log t - 23 / 2) ^ 2) * he
  · have h' : t ∈ Set.Ioi (1000000 : ℝ) := lt_of_not_ge h
    rw [Set.indicator_of_mem h']
    have hψ := euler570_psi_high hRH h'.le
    have hF : 0 ≤ finiteMajor t := by
      unfold finiteMajor; positivity
    unfold highMajor
    linear_combination
      (mul_le_mul hψ hS hS₀ (by positivity)) + hF +
        (Real.log t ^ 2 / 24) * (11 + 16 * (Real.log t - 23 / 2) + 6 * (Real.log t - 23 / 2) ^ 2) *
          he

/-- The finite-error majorant is integrable by three logarithmic moments. -/
private theorem finite_major_integrable {x : ℝ} (hx₁ : 1 ≤ x) :
    MeasureTheory.IntegrableOn finiteMajor (Set.Ioi x) := by
  apply
    ((aux_integrable_quad (d := 11 / 10) (by norm_num only) hx₁ 0 6 16 11 (23 / 2)).const_mul
        (4 / 5 : ℝ)).congr
  exact
    Filter.Eventually.of_forall fun t ↦ by
      simp only [finiteMajor, pow_zero, mul_one,
        show -(11 / 10 : ℝ) - 1 = -(21 / 10) by norm_num only]
      ring

/-- The high-error majorant is integrable by moments of degrees two through four. -/
private theorem high_major_integrable : MeasureTheory.IntegrableOn highMajor (Set.Ioi 1000000) := by
  apply
    ((aux_integrable_quad (d := 11 / 10) (by norm_num only) (by norm_num only : (1 : ℝ) ≤ 1000000) 2
            6 16 11 (23 / 2)).const_mul
        (1 / 24 : ℝ)).congr
  exact
    Filter.Eventually.of_forall fun t ↦ by
      simp only [highMajor, show -(11 / 10 : ℝ) - 1 = -(21 / 10) by norm_num only]
      ring

/-- The centered remainder is integrable at every section 137 cutoff. -/
private theorem profile_error_integrable (hRH : RiemannHypothesis) {x : ℝ} (hx : 1423 ≤ x)
    (hl : 23 / 2 ≤ Real.log x) :
    MeasureTheory.IntegrableOn (fun t ↦ (Chebyshev.psi t - t) * deriv quarterDensity663 t)
      (Set.Ioi x) := by
  have hx₁ : 1 ≤ x := by linarith only [hx]
  have hm := finite_major_integrable hx₁
  have hh := high_major_integrable
  have hi : MeasureTheory.IntegrableOn ((Set.Ioi (1000000 : ℝ)).indicator highMajor) (Set.Ioi x) :=
    (MeasureTheory.integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet).mpr
      (hh.mono_set Set.inter_subset_left)
  refine
    (hm.add hi).mono'
      (((Chebyshev.psi_mono.measurable.sub measurable_id).mul
          (measurable_deriv quarterDensity663)).aestronglyMeasurable)
      ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  exact
    profile_error_major hRH (hx.trans ht.le)
      (hl.trans (Real.log_le_log (zero_lt_one.trans_le hx₁) ht.le))

/-- Under RH, the improper signed Abel identity applies at the section
137 cutoff with no extra integrability hypothesis. -/
theorem quarter_profile_signed_abel_663 (hRH : RiemannHypothesis) {x : ℝ} (hx : 1423 ≤ x)
    (hl : 23 / 2 ≤ Real.log x) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterDensity663 n) -
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * quarterDensity663 n =
      (∫ t in Set.Ioi x, quarterDensity663 t) - (Chebyshev.psi x - x) * quarterDensity663 x -
        ∫ t in Set.Ioi x, (Chebyshev.psi t - t) * deriv quarterDensity663 t :=
  quarter_profile_abel_663 (by linarith only [hx]) (profile_error_integrable hRH hx hl)

/-- The sum of the two improper error majorants in (137.22),
with the exact lower cutoff retained in the finite-envelope term. -/
noncomputable def quarterAbelError663 (x : ℝ) : ℝ :=
  (∫ t in Set.Ioi x, finiteMajor t) + ∫ t in Set.Ioi (1000000 : ℝ), highMajor t

/-- On a section 137 cutoff below one million, the two explicit moments
bound the signed tail error while preserving the exact lower boundary. -/
theorem quarter_profile_tail_upper_663 (hRH : RiemannHypothesis) {x : ℝ} (hx : 1423 ≤ x)
    (hu : x ≤ 1000000) (hl : 23 / 2 ≤ Real.log x) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterDensity663 n) -
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * quarterDensity663 n ≤
      (∫ t in Set.Ioi x, quarterDensity663 t) - (Chebyshev.psi x - x) * quarterDensity663 x +
        quarterAbelError663 x := by
  have hx₁ : 1 ≤ x := by linarith only [hx]
  have hm := finite_major_integrable hx₁
  have hi : MeasureTheory.IntegrableOn ((Set.Ioi (1000000 : ℝ)).indicator highMajor) (Set.Ioi x) :=
    (MeasureTheory.integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet).mpr
      (high_major_integrable.mono_set Set.inter_subset_left)
  have he :=
    MeasureTheory.norm_integral_le_of_norm_le (hm.add hi)
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        exact
          profile_error_major hRH (hx.trans ht.le)
            (hl.trans (Real.log_le_log (zero_lt_one.trans_le hx₁) ht.le)))
  change
    ‖∫ t in Set.Ioi x, (Chebyshev.psi t - t) * deriv quarterDensity663 t‖ ≤
      ∫ t in Set.Ioi x, finiteMajor t + (Set.Ioi (1000000 : ℝ)).indicator highMajor t at he
  rw [Real.norm_eq_abs, MeasureTheory.integral_add hm hi,
    MeasureTheory.setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right hu] at he
  unfold quarterAbelError663
  linarith only [quarter_profile_signed_abel_663 hRH hx hl, (abs_le.mp he).1]

/-- At the section 137 radii, the logarithm of the squared radius lies
in the short interval used for the boundary estimate. -/
private theorem radius_log_box_wide {r : ℝ} (hr : r ∈ Set.Icc 328 333) :
    Real.log (r ^ 2) ∈ Set.Icc (23 / 2) 11.7 := by
  have hx₁ : (107584 : ℝ) ≤ r ^ 2 := by
    rw [show (107584 : ℝ) = 328 ^ 2 by norm_num only]
    exact pow_le_pow_left₀ (by norm_num only) hr.1 2
  have hx₂ : r ^ 2 ≤ (110889 : ℝ) :=
    (pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 328).trans hr.1) hr.2 2).trans
      (by norm_num only)
  have h₁ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 107584) (j := 17) (n := 24) (lo := 23 / 2) (hi :=
        12) (by decide +kernel)).1
  have h₂ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 110889) (j := 17) (n := 24) (lo := 11) (hi :=
        11.7) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h₁ h₂
  exact
    ⟨h₁.trans (Real.log_le_log (by norm_num only) hx₁), by
      linarith only [Real.log_le_log ((by norm_num only : (0 : ℝ) < 107584).trans_le hx₁) hx₂, h₂]⟩

/-- At the lower boundary the profile is negative and bounded below by
-20. Keeping this sign permits a sharp main integral comparison. -/
theorem quarter_profile_boundary_wide_663 {r : ℝ} (hr : r ∈ Set.Icc 328 333) :
    quarterProfile663 (Real.log (r ^ 2)) ∈ Set.Ioo (-20) 0 := by
  have hv := radius_log_box_wide hr
  refine ⟨quarter_profile_gt_neg20_663 hv.1, ?_⟩
  have h₀ := sub_nonneg.mpr hv.1
  have h₁ : Real.log (r ^ 2) - 23 / 2 ≤ 0.2 := by linarith only [hv.2]
  have h := profile_coeff_bounds
  have hb := mul_le_mul_of_nonneg_right h.2.1.2 h₀
  have hc := mul_le_mul_of_nonneg_right h.2.2.2 (sq_nonneg (Real.log (r ^ 2) - 23 / 2))
  rw [profile_expand]
  nlinarith only [h.1.2, hb, hc, h₀, pow_le_pow_left₀ h₀ h₁ 2]

/-- For section 137, the tail is bounded by the signed main integral
plus the square-root boundary allowance and the two improper error moments. -/
theorem quarter_profile_radius_wide_663 (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 333) :
    let x := r ^ 2
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterDensity663 n) -
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * quarterDensity663 n ≤
      (∫ t in Set.Ioi x, quarterDensity663 t) + 16 * x ^ (-(11 / 10) : ℝ) +
        quarterAbelError663 x := by
  intro x
  have hr₀ : (0 : ℝ) ≤ r := (by norm_num only : (0 : ℝ) ≤ 328).trans hr.1
  have hx : 1423 ≤ x :=
    (by norm_num only : (1423 : ℝ) ≤ 328 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr.1 2)
  have hu : x ≤ 1000000 := (pow_le_pow_left₀ hr₀ hr.2 2).trans (by norm_num only)
  have hx₀ : 0 < x := by linarith only [hx]
  have hψ := AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million hx hu
  have hF := quarter_profile_boundary_wide_663 hr
  have hab : |quarterProfile663 (Real.log x)| ≤ 20 :=
    abs_le.mpr ⟨hF.1.le, hF.2.le.trans (by norm_num only)⟩
  have hd := mul_le_mul_of_nonneg_left hab (Real.rpow_nonneg hx₀.le (-(8 / 5)))
  have ht :=
    mul_le_mul hψ hd (mul_nonneg (Real.rpow_nonneg hx₀.le (-(8 / 5))) (abs_nonneg _))
      (by positivity)
  have he : Real.sqrt x * x ^ (-(8 / 5) : ℝ) = x ^ (-(11 / 10) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx₀]
    norm_num only
  have herr : -((Chebyshev.psi x - x) * quarterDensity663 x) ≤ 16 * x ^ (-(11 / 10) : ℝ) := by
    refine (neg_le_abs _).trans ?_
    rw [quarterDensity663, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx₀.le _)]
    linear_combination ht + 16 * he
  have h := quarter_profile_tail_upper_663 hRH hx hu (radius_log_box_wide hr).1
  linarith only [h, herr]

private theorem radius_log_box {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) :
    Real.log (r ^ 2) ∈ Set.Icc (23 / 2) 11.7 := by
  exact radius_log_box_wide ⟨hr.1, hr.2.trans (by norm_num only)⟩

/-- The signed boundary estimate restricted to the quarter-square radii. -/
theorem quarter_profile_boundary_663 {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) :
    quarterProfile663 (Real.log (r ^ 2)) ∈ Set.Ioo (-20) 0 := by
  exact quarter_profile_boundary_wide_663 ⟨hr.1, hr.2.trans (by norm_num only)⟩

/-- The signed Abel estimate restricted to the quarter-square radii. -/
theorem quarter_profile_radius_upper_663 (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) :
    let x := r ^ 2
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterDensity663 n) -
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * quarterDensity663 n ≤
      (∫ t in Set.Ioi x, quarterDensity663 t) + 16 * x ^ (-(11 / 10) : ℝ) +
        quarterAbelError663 x := by
  exact quarter_profile_radius_wide_663 hRH ⟨hr.1, hr.2.trans (by norm_num only)⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
