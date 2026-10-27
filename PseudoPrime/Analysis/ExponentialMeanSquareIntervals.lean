/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteExponentialMeanSquare

/-!
# Interval bounds from weighted exponential mean squares

These estimates use only continuity and integrability of the weighted square.
They do not require any bound on pair correlation or on zero counts.
-/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- The Laplace weight is strictly positive at every displacement.
Use positivity of the real exponential in energy comparisons. -/
theorem weight_pos (v : ℝ) : 0 < weight v := by exact Real.exp_pos _

/-- The Laplace weight is continuous on the real line.
Compose absolute value with multiplication and exponential for interval integrability. -/
theorem continuous_weight : Continuous weight := by
  exact Real.continuous_exp.comp (continuous_const.mul continuous_abs)

/-- Every finite exponential sum with real frequencies and complex coefficients is continuous.
Use continuity of each complex exponential and the finite sum for substitutions. -/
theorem continuous_exponentialSum {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) :
    Continuous (exponentialSum s γ a) := by
  exact
    continuous_finsetSum s
      (fun j hj ↦
        continuous_const.mul
          (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)))

/-- If the integral of a continuous square over a nondegenerate interval is at most its constant
bound times the interval length, some point has squared norm at most that bound. -/
theorem exists_point_sq_le_of_interval_integral {f : ℝ → ℂ} (hf : Continuous f) {a b B : ℝ}
    (hab : a < b) (hI : (∫ x : ℝ in a..b, ‖f x‖ ^ 2) ≤ B * (b - a)) :
    ∃ x ∈ Set.Icc a b, ‖f x‖ ^ 2 ≤ B := by
  by_contra h
  have hbad : ∀ x, x ∈ Set.Icc a b → B < ‖f x‖ ^ 2 := by
    intro x hx
    by_contra hle
    exact h ⟨x, hx, le_of_not_gt hle⟩
  have hc : Continuous (fun y : ℝ => ‖f y‖ ^ 2) := (continuous_norm.comp hf).pow 2
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, le_rfl, hab.le⟩ hc.continuousOn
  have hcontInt : IntervalIntegrable (fun y : ℝ => ‖f y‖ ^ 2) MeasureTheory.volume a b :=
    hc.intervalIntegrable (μ := MeasureTheory.volume) a b
  have hlow : (∫ y : ℝ in a..b, (‖f x‖ ^ 2 : ℝ)) ≤ ∫ y : ℝ in a..b, ‖f y‖ ^ 2 :=
    intervalIntegral.integral_mono_on hab.le intervalIntegrable_const hcontInt (fun y hy ↦ hmin hy)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
  nlinarith only [hlow, hI, hbad x hx, hab]

/-- A mean-square integral bound gives a pointwise upper bound for the real part.
Use a point with small norm and the real-part norm inequality. -/
theorem exists_real_part_le_sqrt_of_interval_integral {f : ℝ → ℂ} (hf : Continuous f) {a b B : ℝ}
    (hab : a < b) (hB : 0 ≤ B) (hI : (∫ x : ℝ in a..b, ‖f x‖ ^ 2) ≤ B * (b - a)) :
    ∃ x ∈ Set.Icc a b, (f x).re ≤ Real.sqrt B := by
  obtain ⟨x, hx, hsq⟩ := exists_point_sq_le_of_interval_integral hf hab hI
  refine ⟨x, hx, ?_⟩
  exact le_trans (Complex.re_le_norm (f x)) ((Real.le_sqrt (norm_nonneg (f x)) hB).mpr hsq)

/-- If c is at least one and 0 ≤ v ≤ log c, exp v is at most c cubed times the weight.
Compare exp(3v) with exp(3 log c); this controls the logarithmic Jacobian. -/
theorem exp_le_cube_mul_weight {c v : ℝ} (hc : 1 ≤ c) (hv : v ∈ Set.Icc 0 (Real.log c)) :
    Real.exp v ≤ c ^ 3 * weight v := by
  have hp : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have he : Real.exp (3 * v) ≤ c ^ 3 := by
    calc
      Real.exp (3 * v) ≤ Real.exp (3 * Real.log c) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv.2 (by norm_num only))
      _ = c ^ 3 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num only, Real.exp_nat_mul, Real.exp_log hp]
  calc
    Real.exp v = Real.exp (3 * v) * weight v := by
      rw [weight, abs_of_nonneg hv.1, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right he (weight_pos v).le

/-- For a nonnegative interval endpoint, the local weighted square is at most the full energy.
Use nonnegativity and integrability to extend the integration set. -/
theorem interval_energy_le {f : ℝ → ℂ}
    (hi : MeasureTheory.Integrable (fun v ↦ ‖f v‖ ^ 2 * weight v)) {b : ℝ} (hb : 0 ≤ b) :
    (∫ v : ℝ in 0..b, ‖f v‖ ^ 2 * weight v) ≤ energy f := by
  rw [intervalIntegral.integral_of_le hb]
  exact
    MeasureTheory.setIntegral_le_integral hi
      (Filter.Eventually.of_forall (fun v ↦ mul_nonneg (sq_nonneg ‖f v‖) (weight_pos v).le))

/-- For a continuous function with integrable weighted square and c ≥ 1, the logarithmic
Jacobian integral is at most c cubed times its energy. Compare densities and integrate. -/
theorem logarithmic_interval_energy_le {f : ℝ → ℂ} (hf : Continuous f)
    (hi : MeasureTheory.Integrable (fun v ↦ ‖f v‖ ^ 2 * weight v)) {c : ℝ} (hc : 1 ≤ c) :
    (∫ v : ℝ in 0..Real.log c, ‖f v‖ ^ 2 * Real.exp v) ≤ c ^ 3 * energy f := by
  have hl : 0 ≤ Real.log c := Real.log_nonneg hc
  have hleft : Continuous (fun v ↦ ‖f v‖ ^ 2 * Real.exp v) := by
    simpa only [Pi.mul_def, Pi.pow_def] using (hf.norm.pow 2).mul Real.continuous_exp
  have hright : Continuous (fun v ↦ c ^ 3 * (‖f v‖ ^ 2 * weight v)) := by
    simpa only [Pi.mul_def, Pi.pow_def] using
      (continuous_const : Continuous (fun _ : ℝ ↦ c ^ 3)).mul
        ((hf.norm.pow 2).mul continuous_weight)
  calc
    _ ≤ ∫ v : ℝ in 0..Real.log c, c ^ 3 * (‖f v‖ ^ 2 * weight v) :=
      intervalIntegral.integral_mono_on hl (hleft.intervalIntegrable _ _)
        (hright.intervalIntegrable _ _)
        (fun v hv ↦ by nlinarith only [exp_le_cube_mul_weight hc hv, sq_nonneg ‖f v‖])
    _ = c ^ 3 * ∫ v : ℝ in 0..Real.log c, ‖f v‖ ^ 2 * weight v :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ c ^ 3 * energy f :=
      mul_le_mul_of_nonneg_left (interval_energy_le hi hl) (pow_nonneg (le_trans zero_le_one hc) 3)

/-- A centered weighted energy bound gives a real-part estimate on the original interval.
On the centered interval of length `d`, the Laplace weight is at least `exp (-d)`. -/
theorem exists_real_part_le_sqrt_on_centered_interval {f : ℝ → ℂ} (hf : Continuous f) {a b : ℝ}
    (hab : a < b)
    (hE : MeasureTheory.Integrable (fun w : ℝ => ‖f (w + (a + b) / 2)‖ ^ 2 * weight w)) :
    ∃ v ∈ Set.Icc a b,
      (f v).re ≤
        Real.sqrt (Real.exp (b - a) * energy (fun w : ℝ => f (w + (a + b) / 2)) / (b - a)) := by
  let d : ℝ := b - a
  let v₀ : ℝ := (a + b) / 2
  have hd : 0 < d := by
    dsimp [d]; linarith only [hab]
  have hleft : v₀ - d / 2 = a := by
    dsimp [v₀, d]; ring
  have hright : v₀ + d / 2 = b := by
    dsimp [v₀, d]; ring
  have hg : Continuous (fun w : ℝ => f (w + v₀)) := hf.comp (continuous_id.add continuous_const)
  have hmono :
    (∫ w : ℝ in -d / 2..d / 2, ‖f (w + v₀)‖ ^ 2) ≤
      ∫ w : ℝ in -d / 2..d / 2, Real.exp d * (‖f (w + v₀)‖ ^ 2 * weight w) :=
    intervalIntegral.integral_mono_on (by linarith only [hd])
      ((hg.norm.pow 2).intervalIntegrable _ _)
      (((continuous_const : Continuous (fun _ : ℝ => Real.exp d)).mul
            ((hg.norm.pow 2).mul continuous_weight)).intervalIntegrable
        _ _)
      (fun w hw ↦ by
        have hwabs : |w| ≤ d / 2 := abs_le.mpr ⟨by linarith only [hw.1], by linarith only [hw.2]⟩
        have hexp : Real.exp (2 * |w|) ≤ Real.exp d :=
          Real.exp_le_exp.mpr (by nlinarith only [hwabs])
        have hEq : 1 = Real.exp (2 * |w|) * weight w := by
          rw [weight, ← Real.exp_add]
          rw [show 2 * |w| + -2 * |w| = 0 by ring, Real.exp_zero]
        have hfact : 1 ≤ Real.exp d * weight w :=
          calc
            1 = Real.exp (2 * |w|) * weight w := hEq
            _ ≤ Real.exp d * weight w := mul_le_mul_of_nonneg_right hexp (weight_pos w).le
        calc
          ‖f (w + v₀)‖ ^ 2 = 1 * ‖f (w + v₀)‖ ^ 2 := by ring
          _ ≤ (Real.exp d * weight w) * ‖f (w + v₀)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hfact (sq_nonneg ‖f (w + v₀)‖)
          _ = Real.exp d * (‖f (w + v₀)‖ ^ 2 * weight w) := by ring)
  have hwhole :
    (∫ w : ℝ in -d / 2..d / 2, ‖f (w + v₀)‖ ^ 2 * weight w) ≤ energy (fun w : ℝ => f (w + v₀)) := by
    rw [intervalIntegral.integral_of_le (by linarith only [hd])]
    exact
      MeasureTheory.setIntegral_le_integral hE
        (Filter.Eventually.of_forall
          (fun w ↦ mul_nonneg (sq_nonneg ‖f (w + v₀)‖) (weight_pos w).le))
  have hI :
    (∫ w : ℝ in -d / 2..d / 2, ‖f (w + v₀)‖ ^ 2) ≤
      (Real.exp d * energy (fun w : ℝ => f (w + v₀)) / d) * d := by
    rw [div_mul_cancel₀ _ hd.ne']
    calc
      _ ≤ ∫ w : ℝ in -d / 2..d / 2, Real.exp d * (‖f (w + v₀)‖ ^ 2 * weight w) := hmono
      _ = Real.exp d * ∫ w : ℝ in -d / 2..d / 2, ‖f (w + v₀)‖ ^ 2 * weight w :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ Real.exp d * energy (fun w : ℝ => f (w + v₀)) :=
        mul_le_mul_of_nonneg_left hwhole (Real.exp_pos d).le
  have hB : 0 ≤ Real.exp d * energy (fun w : ℝ => f (w + v₀)) / d :=
    div_nonneg (mul_nonneg (Real.exp_pos d).le (energy_nonneg _)) hd.le
  have habw : -d / 2 < d / 2 := by nlinarith only [hd]
  have hIw :
    (∫ w : ℝ in -d / 2..d / 2, ‖f (w + v₀)‖ ^ 2) ≤
      (Real.exp d * energy (fun w : ℝ => f (w + v₀)) / d) * (d / 2 - -d / 2) := by
    rw [show d / 2 - -d / 2 = d by ring]
    exact hI
  obtain ⟨w, hw, hsq⟩ := exists_point_sq_le_of_interval_integral hg habw hIw
  have hmem : w + v₀ ∈ Set.Icc a b := by
    rw [← hleft, ← hright]
    exact ⟨by linarith only [hw.1], by linarith only [hw.2]⟩
  refine ⟨w + v₀, hmem, ?_⟩
  exact
    le_trans (Complex.re_le_norm (f (w + v₀)))
      ((Real.le_sqrt (norm_nonneg (f (w + v₀))) hB).mpr hsq)

/-- For a finite exponential sum, bound one point on the centered interval by its shifted Gram
energy. Translate the coefficients by the center phase and apply the weighted mean-square bound. -/
theorem exists_real_part_le_sqrt_translated_exponentialSum {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (a : ι → ℂ) {v₀ d : ℝ} (hd : 0 < d) :
    ∃ w ∈ Set.Icc (-d / 2) (d / 2),
      (exponentialSum s γ a (w + v₀)).re ≤
        Real.sqrt
          (Real.exp d *
              energy (exponentialSum s γ (fun j ↦ a j * Complex.exp (Complex.I * γ j * v₀))) /
            d) := by
  let b : ι → ℂ := fun j ↦ a j * Complex.exp (Complex.I * γ j * v₀)
  let f : ℝ → ℂ := fun w ↦ exponentialSum s γ a (w + v₀)
  have hshift : f = exponentialSum s γ b := by
    funext w
    exact exponentialSum_translate s γ a w v₀
  have hf : Continuous f :=
    continuous_exponentialSum s γ a |>.comp (continuous_id.add continuous_const)
  have hI : MeasureTheory.Integrable (fun w : ℝ ↦ ‖f w‖ ^ 2 * weight w) := by
    have heq :
      (fun w : ℝ ↦ ‖f w‖ ^ 2 * weight w) = (fun w ↦ ‖exponentialSum s γ b w‖ ^ 2 * weight w) := by
      funext w
      rw [hshift]
    rw [heq]
    exact integrable_energy_exponentialSum s γ b
  have hzero : (-d / 2 + d / 2) / 2 = 0 := by ring
  have hI' :
    MeasureTheory.Integrable (fun w : ℝ ↦ ‖f (w + (-d / 2 + d / 2) / 2)‖ ^ 2 * weight w) := by
    simpa only [hzero, add_zero] using hI
  have hcenter :=
    exists_real_part_le_sqrt_on_centered_interval hf (show -d / 2 < d / 2 by linarith only [hd]) hI'
  have henergy : energy f = energy (exponentialSum s γ b) := congrArg energy hshift
  have henergy' :
    energy (fun w : ℝ ↦ f (w + (-d / 2 + d / 2) / 2)) = energy (exponentialSum s γ b) := by
    simpa only [hzero, add_zero] using henergy
  obtain ⟨w, hw, hwbound⟩ := hcenter
  have hwbound' :
    (f w).re ≤ Real.sqrt (Real.exp d * energy (fun z : ℝ ↦ f (z + (-d / 2 + d / 2) / 2)) / d) := by
    simpa only [show d / 2 - -d / 2 = d by ring] using hwbound
  refine ⟨w, hw, ?_⟩
  change (f w).re ≤ _
  calc
    _ ≤ Real.sqrt (Real.exp d * energy (fun z : ℝ ↦ f (z + (-d / 2 + d / 2) / 2)) / d) := hwbound'
    _ = Real.sqrt (Real.exp d * energy (exponentialSum s γ b) / d) := by rw [henergy']

/-- For a continuous function, x > 0 and c ≥ 1, the multiplicative interval integral equals
its logarithmic-coordinate integral. Substitute y = x exp v on the strictly positive image. -/
theorem multiplicative_interval_eq {f : ℝ → ℂ} (hf : Continuous f) {x c : ℝ} (hx : 0 < x)
    (hc : 1 ≤ c) :
    (∫ y : ℝ in x..c * x, ‖f (Real.log (y / x))‖ ^ 2) =
      x * ∫ v : ℝ in 0..Real.log c, ‖f v‖ ^ 2 * Real.exp v := by
  have hg :
    ContinuousOn (fun y : ℝ ↦ ‖f (Real.log (y / x))‖ ^ 2)
      ((fun v : ℝ ↦ x * Real.exp v) '' Set.uIcc 0 (Real.log c)) := by
    apply ContinuousOn.pow
    apply ContinuousOn.norm
    apply hf.comp_continuousOn
    apply ContinuousOn.log (continuous_id.div_const x).continuousOn
    rintro y ⟨v, hv, rfl⟩
    exact div_ne_zero (mul_ne_zero hx.ne' (Real.exp_ne_zero v)) hx.ne'
  have he :=
    intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := Real.log c) (f := fun v : ℝ ↦
      x * Real.exp v) (f' := fun v : ℝ ↦ x * Real.exp v) (g := fun y : ℝ ↦
      ‖f (Real.log (y / x))‖ ^ 2) (fun v hv ↦ (Real.hasDerivAt_exp v).const_mul x)
      (continuous_const.mul Real.continuous_exp).continuousOn hg
  simp only [Function.comp_def, mul_div_cancel_left₀ _ hx.ne', Real.log_exp, Real.exp_zero, mul_one,
    Real.exp_log (lt_of_lt_of_le zero_lt_one hc)] at he
  rw [mul_comm c x, ← he, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  ring

/-- For a continuous function with integrable weighted square, x > 0 and c ≥ 1, its
multiplicative interval mean square is at most x c cubed times its energy.
Combine the logarithmic substitution with the density comparison. -/
theorem multiplicative_interval_energy_le {f : ℝ → ℂ} (hf : Continuous f)
    (hi : MeasureTheory.Integrable (fun v ↦ ‖f v‖ ^ 2 * weight v)) {x c : ℝ} (hx : 0 < x)
    (hc : 1 ≤ c) : (∫ y : ℝ in x..c * x, ‖f (Real.log (y / x))‖ ^ 2) ≤ x * c ^ 3 * energy f := by
  rw [multiplicative_interval_eq hf hx hc]
  have h := mul_le_mul_of_nonneg_left (logarithmic_interval_energy_le hf hi hc) hx.le
  simpa only [mul_assoc] using h

/-- For finite exponential sums, the multiplicative interval mean square is bounded by
x c cubed times the rational-kernel energy. Supply actual continuity and integrability. -/
theorem exponentialSum_multiplicative_interval_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ)
    {x c : ℝ} (hx : 0 < x) (hc : 1 ≤ c) :
    (∫ y : ℝ in x..c * x, ‖exponentialSum s γ a (Real.log (y / x))‖ ^ 2) ≤
      x * c ^ 3 * energy (exponentialSum s γ a) := by
  exact
    multiplicative_interval_energy_le (continuous_exponentialSum s γ a)
      (integrable_energy_exponentialSum s γ a) hx hc

end PseudoPrime.Analysis.ExponentialMeanSquare
