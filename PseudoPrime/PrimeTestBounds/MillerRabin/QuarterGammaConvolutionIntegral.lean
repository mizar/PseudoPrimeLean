/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaProfile
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GammaOneSided
public import PseudoPrime.Analysis.ExponentialMomentTail

/-! # Positive-half-line Gamma convolution -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The shifted profile convolved with an exponential of rate `c`, over
the profile's positive support. This is the individual pole contribution
used in the even-Gamma tail estimate. -/
noncomputable def quarterGammaConvolution (z c : ℝ) : ℝ :=
  ∫ v in Set.Ioi (0 : ℝ), quarterGammaDensity v * Real.exp (-c * |v - z|)

/-- The explicit lower contribution of the first Gamma pole at shifted
scale `z`. It is the normalized initial fifth exponential moment, expressed
as a complete moment minus its tail. -/
noncomputable def quarterGammaFirstCorrection (z : ℝ) : ℝ :=
  (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-(1 / 2 : ℝ) * z)) *
    (Analysis.logPowerTailPoly (29 / 50) 5 0 -
      Real.exp (-(29 / 50 : ℝ) * z) * Analysis.logPowerTailPoly (29 / 50) 5 z)

/-- The positive-support convolution is integrable for nonnegative decay
rate. Its kernel is bounded by one and the fifth exponential moment supplies
an integrable majorant. -/
theorem quarter_gamma_convolution_integrable (z : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    MeasureTheory.IntegrableOn (fun v : ℝ ↦ quarterGammaDensity v * Real.exp (-c * |v - z|))
      (Set.Ioi 0) := by
  have hi' :
    MeasureTheory.IntegrableOn (fun v : ℝ ↦ v ^ 5 * Real.exp (-(27 / 25 : ℝ) * v)) (Set.Ioi 0) :=
    Analysis.exponential_moment_integrable (by norm_num only) 5
  let f : ℝ → ℝ := fun v ↦
    ((27 / 25 : ℝ) ^ 5 / 120) * v ^ 5 * Real.exp (-(27 / 25 : ℝ) * v) * Real.exp (-c * |v - z|)
  have hcont : Continuous f := by
    dsimp only [f]
    fun_prop
  have hmajor := hi'.const_mul ((27 / 25 : ℝ) ^ 5 / 120)
  have hf : MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
    refine hmajor.mono' (hcont.continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro v hv
    have hvpos : 0 < v := hv
    have hbase : 0 ≤ ((27 / 25 : ℝ) ^ 5 / 120) * v ^ 5 * Real.exp (-(27 / 25 : ℝ) * v) := by
      positivity
    have he : Real.exp (-c * |v - z|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (abs_nonneg _))
    dsimp only [f]
    rw [Real.norm_of_nonneg (mul_nonneg hbase (Real.exp_pos _).le)]
    simpa only [mul_assoc] using mul_le_of_le_one_right hbase he
  apply hf.congr_fun _ measurableSet_Ioi
  intro v hv
  dsimp only [f, quarterGammaDensity]
  rw [ite_eq_left hv.le]

/-- The real part of the normalized positive-pole resolvent equals its
positive-half-line density convolution, with the exact factors of `c` and
`2π`. Integrability justifies moving the real embedding through the integral. -/
theorem quarter_pole_convolution_real (y : ℝ) {c : ℝ} (hc : 0 < c) :
    (1 / (2 * Real.pi)) * c ^ 2 *
        (∫ t : ℝ,
            (refinedSixPoleKernel.function (Complex.I * t) *
                Complex.exp (Complex.I * (t : ℂ) * y)) *
              ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)).re =
      (c / 2) * quarterGammaConvolution (y + 21 / 8) c := by
  have h := quarter_pole_density_positive y hc
  have hi := quarter_gamma_convolution_integrable (y + 21 / 8) hc.le
  have hcast := Complex.ofRealCLM.integral_comp_comm hi
  change
    (∫ v in Set.Ioi (0 : ℝ),
        ((quarterGammaDensity v * Real.exp (-c * |v - (y + 21 / 8)|) : ℝ) : ℂ)) =
      ((quarterGammaConvolution (y + 21 / 8) c : ℝ) : ℂ) at hcast
  simp only [Complex.ofReal_mul] at hcast
  rw [hcast] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    mul_zero, add_zero, sub_zero] using hr

/-- The part of the convolution on `(0, z]` is a lower bound for the whole
convolution when the decay rate is nonnegative. On this interval the absolute
value simplifies to `z - v`, preparing the first-pole estimate. -/
theorem quarter_gamma_convolution_lower {z c : ℝ} (hc : 0 ≤ c) :
    (∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity v * Real.exp (-c * (z - v))) ≤
      quarterGammaConvolution z c := by
  have hi := quarter_gamma_convolution_integrable z hc
  have hn : ∀ v : ℝ, 0 ≤ quarterGammaDensity v * Real.exp (-c * |v - z|) := by
    intro v
    have hd : 0 ≤ quarterGammaDensity v := by
      by_cases hv : 0 ≤ v
      · rw [quarterGammaDensity, ite_eq_left hv]
        positivity
      · rw [quarterGammaDensity, ite_eq_right hv]
    exact mul_nonneg hd (Real.exp_pos _).le
  have hb :=
    MeasureTheory.setIntegral_mono_set hi (Filter.Eventually.of_forall hn)
      (Filter.Eventually.of_forall (fun v (hv : v ∈ Set.Ioc (0 : ℝ) z) ↦ hv.1))
  have he :
    (∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity v * Real.exp (-c * |v - z|)) =
      ∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity v * Real.exp (-c * (z - v)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    dsimp only
    rw [abs_of_nonpos (sub_nonpos.mpr hv.2), neg_sub]
  change _ ≤ quarterGammaConvolution z c
  rw [← he]
  exact hb

/-- The explicit initial piece of a positive-pole convolution is a lower
bound for the real resolvent integral. This is the finite integral used to
retain the first even-Gamma pole. -/
theorem quarter_pole_initial_lower (y : ℝ) {c : ℝ} (hc : 0 < c) :
    (c / 2) *
        (∫ v in Set.Ioc (0 : ℝ) (y + 21 / 8),
          quarterGammaDensity v * Real.exp (-c * (y + 21 / 8 - v))) ≤
      (1 / (2 * Real.pi)) * c ^ 2 *
        (∫ t : ℝ,
            (refinedSixPoleKernel.function (Complex.I * t) *
                Complex.exp (Complex.I * (t : ℂ) * y)) *
              ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)).re := by
  rw [quarter_pole_convolution_real y hc]
  exact
    mul_le_mul_of_nonneg_left (quarter_gamma_convolution_lower hc.le)
      (div_nonneg hc.le (by norm_num only))

/-- On the initial interval, the density and pole exponential combine into
one fifth exponential moment with rate `27/25 - c`. The scale-dependent
factor is constant and can be evaluated separately. -/
theorem quarter_gamma_initial_moment (z c : ℝ) :
    (∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity v * Real.exp (-c * (z - v))) =
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-c * z)) *
        ∫ v in Set.Ioc (0 : ℝ) z, v ^ 5 * Real.exp (-((27 / 25 : ℝ) - c) * v) := by
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro v hv
  dsimp only
  rw [quarterGammaDensity, ite_eq_left hv.1.le]
  have he : -(27 / 25 : ℝ) * v + -c * (z - v) = -c * z + -((27 / 25 : ℝ) - c) * v := by ring
  have hexp :
    Real.exp (-(27 / 25 : ℝ) * v) * Real.exp (-c * (z - v)) =
      Real.exp (-c * z) * Real.exp (-((27 / 25 : ℝ) - c) * v) := by
    rw [← Real.exp_add, he, Real.exp_add]
  have hm := congrArg (fun x : ℝ ↦ ((27 / 25 : ℝ) ^ 5 / 120) * v ^ 5 * x) hexp
  nlinarith only [hm]

/-- For `z ≥ 0`, the first Gamma pole contributes at least the complete
fifth exponential moment minus its tail. The tail polynomial is exact and
the decay rate is `29/50`. -/
theorem quarter_first_pole_moment {z : ℝ} (hz : 0 ≤ z) :
    (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-(1 / 2 : ℝ) * z)) *
        (Analysis.logPowerTailPoly (29 / 50) 5 0 -
          Real.exp (-(29 / 50 : ℝ) * z) * Analysis.logPowerTailPoly (29 / 50) 5 z) ≤
      quarterGammaConvolution z (1 / 2) := by
  have h := quarter_gamma_convolution_lower (z := z) (c := (1 / 2 : ℝ)) (by norm_num only)
  rw [quarter_gamma_initial_moment,
    Analysis.exponential_moment_interval (by norm_num only) hz 5] at h
  norm_num only at h ⊢
  exact h

/-- The first-pole correction is nonnegative at every nonnegative shifted
scale, since it is a positive factor times an integral of a nonnegative
exponential fifth moment. -/
theorem quarter_gamma_first_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ quarterGammaFirstCorrection z := by
  have hi : 0 ≤ ∫ v in Set.Ioc (0 : ℝ) z, v ^ 5 * Real.exp (-(29 / 50 : ℝ) * v) := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioc
    intro v hv
    exact mul_nonneg (pow_nonneg hv.1.le _) (Real.exp_pos _).le
  rw [Analysis.exponential_moment_interval (by norm_num only) hz 5] at hi
  unfold quarterGammaFirstCorrection
  exact mul_nonneg (by positivity) hi

/-- The real resolvent integral at the first even-Gamma pole dominates the
explicit fifth-moment lower bound whenever the shifted scale is nonnegative.
This connects the finite exponential moment to the actual Fourier integral. -/
theorem quarter_first_pole_resolvent {y : ℝ} (hy : 0 ≤ y + 21 / 8) :
    (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-(1 / 2 : ℝ) * (y + 21 / 8))) *
        (Analysis.logPowerTailPoly (29 / 50) 5 0 -
          Real.exp (-(29 / 50 : ℝ) * (y + 21 / 8)) *
            Analysis.logPowerTailPoly (29 / 50) 5 (y + 21 / 8)) ≤
      (1 / (2 * Real.pi)) *
        (∫ t : ℝ,
            (refinedSixPoleKernel.function (Complex.I * t) *
                Complex.exp (Complex.I * (t : ℂ) * y)) *
              ((1 / (1 / 4 + t ^ 2) : ℝ) : ℂ)).re := by
  have h := quarter_first_pole_moment hy
  have he := quarter_pole_convolution_real y (c := (1 / 2 : ℝ)) (by norm_num only)
  norm_num only at h he ⊢
  nlinarith only [h, he]

/-- The first-pole lower bound in terms of the real phase used by the
one-sided Gamma estimate. The phase integral is the real part of the complex
resolvent, so the finite moment bound transfers without changing its constant. -/
theorem quarter_first_phase_resolvent {y : ℝ} (hy : 0 ≤ y + 21 / 8) :
    (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-(1 / 2 : ℝ) * (y + 21 / 8))) *
        (Analysis.logPowerTailPoly (29 / 50) 5 0 -
          Real.exp (-(29 / 50 : ℝ) * (y + 21 / 8)) *
            Analysis.logPowerTailPoly (29 / 50) 5 (y + 21 / 8)) ≤
      (1 / (2 * Real.pi)) * ∫ t : ℝ, target028GammaPhase y t / (1 / 4 + t ^ 2) := by
  rw [quarter_phase_resolvent_eq]
  exact quarter_first_pole_resolvent hy

/-- For an even character, subtract the explicit first-pole moment from the
usual second-moment Gamma budget. The logarithmic scale must place the
shifted convolution center on the nonnegative half-line. -/
theorem quarter_gamma_central_first_pole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (he : χ.Even) {x : ℝ} (hx : 0 < x) (hy : 0 ≤ Real.log x + 21 / 8) :
    (refinedCentralGammaPair χ x).re +
        (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-(1 / 2 : ℝ) * (Real.log x + 21 / 8))) *
          (Analysis.logPowerTailPoly (29 / 50) 5 0 -
            Real.exp (-(29 / 50 : ℝ) * (Real.log x + 21 / 8)) *
              Analysis.logPowerTailPoly (29 / 50) 5 (Real.log x + 21 / 8)) ≤
      (13 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 := by
  have h := quarter_gamma_central_with_pole χ he hx
  have hl := quarter_first_phase_resolvent hy
  have hh :
    (∫ t : ℝ, target028GammaPhase (Real.log x) t / (1 / 4 + t ^ 2)) / (2 * Real.pi) =
      (1 / (2 * Real.pi)) * ∫ t : ℝ, target028GammaPhase (Real.log x) t / (1 / 4 + t ^ 2) := by
    ring
  rw [hh] at h
  linarith only [h, hl]

end PseudoPrime.PrimeTestBounds.MillerRabin
