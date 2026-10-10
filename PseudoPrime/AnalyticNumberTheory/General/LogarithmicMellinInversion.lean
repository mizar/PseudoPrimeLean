/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinWeights
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Logarithmic Mellin inversion for coefficient L-series

Absolute convergence at a positive vertical coordinate controls the integral norms termwise.
Mellin inversion and the series-integral interchange give a general logarithmic Perron integral.
Real coefficient shifts translate the L-series argument and retain the same Mellin denominator.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The nth logarithmic Mellin integrand on the vertical line with real coordinate tau.
Multiply the coefficient and n^(-s) by x^s/s^2. Positive x and tau are used for inversion;
a zero coefficient at index zero removes the totalized power's endpoint contribution. -/
noncomputable def logarithmicMellinTerm (a : ℕ → ℂ) (x τ : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  a n * (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I)) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
    ((τ : ℂ) + y * Complex.I) ^ 2

/-- The real part of the vertical argument tau+iy is tau.
Expand real and imaginary parts. This identifies the exponents in norm estimates. -/
private theorem vertical_re (τ y : ℝ) : ((τ : ℂ) + y * Complex.I).re = τ := by
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]

/-- For positive x and nonzero n, the integrand norm factors into the coefficient norm,
n^(-tau), x^tau and the inverse-square vertical kernel norm.
Use the norm formula for positive-real complex powers. This gives the common integral majorant. -/
theorem norm_logarithmicMellinTerm (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) (τ : ℝ) {n : ℕ} (hn : n ≠ 0)
    (y : ℝ) :
    ‖logarithmicMellinTerm a x τ n y‖ =
      ‖a n‖ * (n : ℝ) ^ (-τ) * x ^ τ * ‖(((τ : ℂ) + y * Complex.I) ^ 2)⁻¹‖ := by
  unfold logarithmicMellinTerm
  rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re, vertical_re]

/-- For positive x and tau and nonzero n, Mellin inversion identifies the weighted coefficient
with the normalized integral of its logarithmic Mellin term.
Pull the coefficient through the integral and split the positive ratio's complex power.
This is the termwise input to the series-integral interchange. -/
theorem logarithmicMellinTerm_integral (a : ℕ → ℂ) {x τ : ℝ} (hx : 0 < x) (hτ : 0 < τ) {n : ℕ}
    (hn : n ≠ 0) :
    a n * mellinWeightTwo ((n : ℝ) / x) =
      (2 * Real.pi : ℝ)⁻¹ • ∫ y : ℝ, logarithmicMellinTerm a x τ n y := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hm := mellinInv_mellinWeightTwo_eq (σ := τ) hτ (div_pos hnpos hx)
  have hw :
    mellinWeightTwo ((n : ℝ) / x) =
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ y : ℝ,
          (((n : ℝ) / x : ℝ) : ℂ) ^ (-((τ : ℂ) + y * Complex.I)) *
            (1 / ((τ : ℂ) + y * Complex.I) ^ 2) := by
    rw [← hm]
    simp only [mellinInv, smul_eq_mul, one_div]
  rw [hw, mul_smul_comm]
  congr 1
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  rw [cpow_div_eq_cpow_mul_cpow_neg hnpos.le hx, neg_neg, Complex.ofReal_natCast]
  unfold logarithmicMellinTerm
  ring

/-- The inverse-square kernel is integrable on a vertical line of positive real coordinate.
Rewrite the established Mellin-kernel integrability using inverse powers.
This supplies the integrable factor for coefficient terms. -/
private theorem integrable_vertical_inverse_sq {τ : ℝ} (hτ : 0 < τ) :
    MeasureTheory.Integrable (fun y : ℝ ↦ (((τ : ℂ) + y * Complex.I) ^ 2)⁻¹) := by
  have h := verticalIntegrable_mellinLogKernel hτ.ne'
  unfold Complex.VerticalIntegrable at h
  simpa only [inv_pow] using h

/-- The coefficient amplitude has constant norm along the vertical line.
Positive-real complex powers depend in norm only on the real coordinate.
This bounds each term by a constant multiple of the inverse-square kernel. -/
private theorem norm_logarithmicMellinAmplitude (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) (τ : ℝ) {n : ℕ}
    (hn : n ≠ 0) (y : ℝ) :
    ‖a n * (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I)) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I)‖ =
      ‖a n‖ * (n : ℝ) ^ (-τ) * x ^ τ := by
  rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re, vertical_re]

/-- For positive x and tau and a vanishing coefficient at zero, every coefficient integrand
is integrable. The zero term vanishes; each remaining amplitude is continuous and bounded,
so its product with the integrable inverse-square kernel is integrable. -/
theorem integrable_logarithmicMellinTerm (a : ℕ → ℂ) (ha : a 0 = 0) {x τ : ℝ} (hx : 0 < x)
    (hτ : 0 < τ) (n : ℕ) : MeasureTheory.Integrable (logarithmicMellinTerm a x τ n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have hz : logarithmicMellinTerm a x τ 0 = fun _ ↦ 0 := by
      funext y
      simp only [logarithmicMellinTerm, ha, zero_mul, zero_div]
    rw [hz]
    exact MeasureTheory.integrable_zero _ _ _
  · have hline : Continuous (fun y : ℝ ↦ (τ : ℂ) + y * Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hc :
      Continuous
        (fun y : ℝ ↦
          a n * (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I)) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I)) :=
      (continuous_const.mul (hline.neg.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn)))).mul
        (hline.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')))
    have he :
      logarithmicMellinTerm a x τ n = fun y : ℝ ↦
        (((τ : ℂ) + y * Complex.I) ^ 2)⁻¹ *
          (a n * (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I)) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I)) := by
      funext y
      unfold logarithmicMellinTerm
      ring
    rw [he]
    apply (integrable_vertical_inverse_sq hτ).mul_bdd hc.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun y ↦ (norm_logarithmicMellinAmplitude a hx τ hn y).le)

/-- For positive x and a nonzero index, the integral norm of the coefficient term is bounded
by its constant amplitude times the inverse-square kernel's integral norm.
Factor the pointwise norm and pull its real constant out of the integral.
This provides the summable L1 majorant. -/
theorem integral_norm_logarithmicMellinTerm_le (a : ℕ → ℂ) {x τ : ℝ} (hx : 0 < x) {n : ℕ}
    (hn : n ≠ 0) :
    (∫ y : ℝ, ‖logarithmicMellinTerm a x τ n y‖) ≤
      (‖a n‖ * (n : ℝ) ^ (-τ) * x ^ τ) * ∫ y : ℝ, ‖(((τ : ℂ) + y * Complex.I) ^ 2)⁻¹‖ := by
  rw [show
      (fun y : ℝ ↦ ‖logarithmicMellinTerm a x τ n y‖) =
        (fun y : ℝ ↦ (‖a n‖ * (n : ℝ) ^ (-τ) * x ^ τ) * ‖(((τ : ℂ) + y * Complex.I) ^ 2)⁻¹‖)
      from funext (norm_logarithmicMellinTerm a hx τ hn)]
  rw [MeasureTheory.integral_const_mul]

/-- For a coefficient sequence vanishing at zero, the real-line series term norm is
norm(a n) times n^(-tau). Separate the zero endpoint and apply the positive-real power formula.
This converts absolute series convergence to the coefficient majorant. -/
private theorem norm_LSeries_term_real (a : ℕ → ℂ) (ha : a 0 = 0) (τ : ℝ) (n : ℕ) :
    ‖LSeries.term a (τ : ℂ) n‖ = ‖a n‖ * (n : ℝ) ^ (-τ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, ha, norm_zero, zero_mul]
  · rw [LSeries.term_def₀ ha, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
      Complex.neg_re, Complex.ofReal_re]

/-- Absolute convergence of the coefficient L-series at tau makes the integrals of term norms
summable, for positive x. Convert the series term norms to real powers and apply the
constant integral majorant; the index-zero integrand vanishes.
This justifies exchanging the coefficient series and vertical integral. -/
theorem summable_integral_norm_logarithmicMellinTerm (a : ℕ → ℂ) (ha : a 0 = 0) {x τ : ℝ}
    (hx : 0 < x) (hsum : LSeriesSummable a (τ : ℂ)) :
    Summable (fun n : ℕ ↦ ∫ y : ℝ, ‖logarithmicMellinTerm a x τ n y‖) := by
  have hweight : Summable (fun n : ℕ ↦ ‖a n‖ * (n : ℝ) ^ (-τ)) :=
    (summable_norm_iff.mpr hsum).congr (norm_LSeries_term_real a ha τ)
  apply
    Summable.of_nonneg_of_le (fun n ↦ MeasureTheory.integral_nonneg (fun y ↦ norm_nonneg _)) _
      (hweight.mul_right (x ^ τ * ∫ y : ℝ, ‖(((τ : ℂ) + y * Complex.I) ^ 2)⁻¹‖))
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [logarithmicMellinTerm, ha, zero_mul, zero_div, norm_zero,
      MeasureTheory.integral_zero, Std.le_refl]
  · exact (integral_norm_logarithmicMellinTerm_le a hx hn).trans_eq (by ring)

/-- The total coefficient integrand equals the coefficient L-series times x^s/s^2.
A vanishing coefficient at zero identifies the totalized series terms. Extract the constant
power and denominator from the sum. No convergence premise is needed for this algebraic identity. -/
theorem tsum_logarithmicMellinTerm (a : ℕ → ℂ) (ha : a 0 = 0) (x τ y : ℝ) :
    (∑' n : ℕ, logarithmicMellinTerm a x τ n y) =
      LSeries a ((τ : ℂ) + y * Complex.I) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
        ((τ : ℂ) + y * Complex.I) ^ 2 := by
  unfold logarithmicMellinTerm
  rw [tsum_div_const, tsum_mul_right, LSeries_def₀ ha]
  congr 2
  apply tsum_congr
  intro n
  rw [Complex.cpow_neg, div_eq_mul_inv]

/-- For positive x and tau and an absolutely convergent coefficient L-series at tau,
the logarithmic Mellin-weighted series equals the normalized vertical L-series integral.
The coefficient at zero vanishes. Termwise inversion and the summable integral-norm majorant
justify interchange. This supports real shifts without a character-specific hypothesis. -/
theorem mellinWeightTwo_tsum_eq_integral_LSeries (a : ℕ → ℂ) (ha : a 0 = 0) {x τ : ℝ} (hx : 0 < x)
    (hτ : 0 < τ) (hsum : LSeriesSummable a (τ : ℂ)) :
    (∑' n : ℕ, a n * mellinWeightTwo ((n : ℝ) / x)) =
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ y : ℝ,
          LSeries a ((τ : ℂ) + y * Complex.I) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            ((τ : ℂ) + y * Complex.I) ^ 2 := by
  have hterm :
    ∀ n : ℕ,
      a n * mellinWeightTwo ((n : ℝ) / x) =
        (2 * Real.pi : ℝ)⁻¹ • ∫ y : ℝ, logarithmicMellinTerm a x τ n y := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [ha, zero_mul, logarithmicMellinTerm, zero_div, MeasureTheory.integral_zero,
        smul_zero]
    · exact logarithmicMellinTerm_integral a hx hτ hn
  rw [tsum_congr hterm, tsum_const_smul'' (2 * Real.pi : ℝ)⁻¹,
    (MeasureTheory.hasSum_integral_of_summable_integral_norm
        (integrable_logarithmicMellinTerm a ha hx hτ)
        (summable_integral_norm_logarithmicMellinTerm a ha hx hsum)).tsum_eq]
  congr 1
  exact
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (tsum_logarithmicMellinTerm a ha x τ))

/-- Shift a coefficient sequence by the real power n^(-sigma).
Its L-series at s is the original series at sigma+s, away from the ignored zero endpoint.
This introduces the real shift needed in the logarithmic Perron formula. -/
noncomputable def shiftedLSeriesCoefficient (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) : ℂ :=
  a n * (n : ℂ) ^ (-(σ : ℂ))

/-- A real coefficient shift translates the L-series argument termwise.
At zero both series terms vanish; elsewhere combine the nonzero-base complex powers.
This transfers both convergence and the summed function. -/
private theorem LSeries_term_shift (a : ℕ → ℂ) (σ : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (shiftedLSeriesCoefficient a σ) s n = LSeries.term a ((σ : ℂ) + s) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, LSeries.term_zero]
  · rw [LSeries.term_def, LSeries.term_def, ite_eq_right hn, ite_eq_right hn,
      shiftedLSeriesCoefficient, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn), Complex.cpow_neg]
    ring

/-- The L-series of the shifted coefficients equals the original L-series at sigma+s.
Sum the termwise power identity. This identifies the shifted logarithmic derivative. -/
theorem LSeries_shiftedLSeriesCoefficient (a : ℕ → ℂ) (σ : ℝ) (s : ℂ) :
    LSeries (shiftedLSeriesCoefficient a σ) s = LSeries a ((σ : ℂ) + s) := by
  exact tsum_congr (LSeries_term_shift a σ s)

/-- The shifted coefficient series converges at s exactly when the original series converges
at sigma+s. Rewrite the summability predicate by the termwise power identity.
This supplies the shifted contour's right-half-plane condition. -/
theorem LSeriesSummable_shiftedLSeriesCoefficient (a : ℕ → ℂ) (σ : ℝ) (s : ℂ) :
    LSeriesSummable (shiftedLSeriesCoefficient a σ) s ↔ LSeriesSummable a ((σ : ℂ) + s) := by
  rw [LSeriesSummable, LSeriesSummable, funext (LSeries_term_shift a σ s)]

/-- For positive x and tau, coefficients vanishing at zero, and convergence at sigma+tau,
the series weighted by n^(-sigma) and the logarithmic Mellin weight equals the normalized
vertical integral with the original L-series at sigma+tau+iy.
Apply unshifted inversion to shifted coefficients and translate the series argument. -/
theorem mellinWeightTwo_shifted_tsum_eq_integral_LSeries (a : ℕ → ℂ) (ha : a 0 = 0) (σ : ℝ)
    {x τ : ℝ} (hx : 0 < x) (hτ : 0 < τ) (hsum : LSeriesSummable a ((σ + τ : ℝ) : ℂ)) :
    (∑' n : ℕ, a n * (n : ℂ) ^ (-(σ : ℂ)) * mellinWeightTwo ((n : ℝ) / x)) =
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ y : ℝ,
          LSeries a (((σ + τ : ℝ) : ℂ) + y * Complex.I) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            ((τ : ℂ) + y * Complex.I) ^ 2 := by
  have ha0 : shiftedLSeriesCoefficient a σ 0 = 0 := by rw [shiftedLSeriesCoefficient, ha, zero_mul]
  have hs : LSeriesSummable (shiftedLSeriesCoefficient a σ) (τ : ℂ) :=
    (LSeriesSummable_shiftedLSeriesCoefficient a σ (τ : ℂ)).mpr
      (by simpa only [Complex.ofReal_add] using hsum)
  rw [show
      (fun n ↦ a n * (n : ℂ) ^ (-(σ : ℂ)) * mellinWeightTwo ((n : ℝ) / x)) =
        (fun n ↦ shiftedLSeriesCoefficient a σ n * mellinWeightTwo ((n : ℝ) / x))
      from rfl,
    mellinWeightTwo_tsum_eq_integral_LSeries _ ha0 hx hτ hs]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  rw [LSeries_shiftedLSeriesCoefficient, Complex.ofReal_add, add_assoc]

/-- The finite logarithmic weighted sum over positive natural indices at most floor x.
Each coefficient is multiplied by log(x/n). This is the arithmetic side of Mellin inversion. -/
noncomputable def logarithmicWeightedSum (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n * (Real.log (x / (n : ℝ)) : ℂ)

/-- For positive x and coefficients vanishing at zero, the Mellin-weighted total sum is the
finite logarithmic sum. The weight vanishes beyond x and becomes log(x/n) within the cutoff.
This collapse needs no analytic convergence hypothesis. -/
theorem mellinWeightTwo_tsum_eq_logarithmicWeightedSum (a : ℕ → ℂ) (ha : a 0 = 0) {x : ℝ}
    (hx : 0 < x) :
    (∑' n : ℕ, a n * mellinWeightTwo ((n : ℝ) / x)) = logarithmicWeightedSum a x := by
  have hvanish : ∀ n ∉ Finset.Ioc 0 ⌊x⌋₊, a n * mellinWeightTwo ((n : ℝ) / x) = 0 := by
    intro n hn
    simp only [Finset.mem_Ioc, not_and, not_le] at hn
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · rw [hn0, ha, zero_mul]
    · have hnxlt : x < n := (Nat.floor_lt hx.le).mp (hn hn0)
      have ht : 0 < (n : ℝ) / x := div_pos (by exact_mod_cast hn0) hx
      rw [mellinWeightTwo_eq_ofReal_neg_log_min ht, min_eq_right ((one_le_div hx).mpr hnxlt.le),
        Real.log_one, neg_zero, Complex.ofReal_zero, mul_zero]
  rw [tsum_eq_sum hvanish, logarithmicWeightedSum]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn0, hnx⟩ := Finset.mem_Ioc.mp hn
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  have ht : 0 < (n : ℝ) / x := div_pos hnpos hx
  have hlog : Real.log ((n : ℝ) / x) = -Real.log (x / (n : ℝ)) := by
    rw [← inv_div x (n : ℝ), Real.log_inv]
  rw [mellinWeightTwo_eq_ofReal_neg_log_min ht,
    min_eq_left ((div_le_one hx).mpr ((Nat.le_floor_iff hx.le).mp hnx)), hlog, neg_neg]

/-- Under convergence at sigma+tau, positive x and tau, and a vanishing coefficient at zero,
the finite n^(-sigma)-weighted logarithmic sum equals the normalized shifted vertical integral.
Combine the finite-support collapse with shifted series inversion.
This is the right-edge identity used before shifted residue evaluation. -/
theorem logarithmicWeightedSum_shifted_eq_integral_LSeries (a : ℕ → ℂ) (ha : a 0 = 0) (σ : ℝ)
    {x τ : ℝ} (hx : 0 < x) (hτ : 0 < τ) (hsum : LSeriesSummable a ((σ + τ : ℝ) : ℂ)) :
    logarithmicWeightedSum (shiftedLSeriesCoefficient a σ) x =
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ y : ℝ,
          LSeries a (((σ + τ : ℝ) : ℂ) + y * Complex.I) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            ((τ : ℂ) + y * Complex.I) ^ 2 := by
  have ha0 : shiftedLSeriesCoefficient a σ 0 = 0 := by rw [shiftedLSeriesCoefficient, ha, zero_mul]
  rw [← mellinWeightTwo_tsum_eq_logarithmicWeightedSum _ ha0 hx]
  exact mellinWeightTwo_shifted_tsum_eq_integral_LSeries a ha σ hx hτ hsum

/-- For `τ > 0` and `x > 1`, the kernel `x^z/z²`, with `z = τ + iy`, is integrable
in real `y`, and its integral divided by `2π` equals `log x`. Apply logarithmic
Mellin inversion to the coefficient supported at one. This evaluates the constant
logarithmic-derivative term in centered contour identities. -/
theorem logarithmicMellin_integrable_and_integral {τ x : ℝ} (hτ : 0 < τ) (hx : 1 < x) :
    MeasureTheory.Integrable
        (fun y : ℝ ↦ (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) / ((τ : ℂ) + y * Complex.I) ^ 2) ∧
      (2 * Real.pi)⁻¹ •
          (∫ y : ℝ, (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) / ((τ : ℂ) + y * Complex.I) ^ 2) =
        (Real.log x : ℂ) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  let a : ℕ → ℂ := fun n ↦ if n = 1 then 1 else 0
  have ha : a 0 = 0 := by simp only [a, ite_eq_right Nat.zero_ne_one]
  have hg := integrable_logarithmicMellinTerm a ha hx0 hτ 1
  change MeasureTheory.Integrable (fun y ↦ logarithmicMellinTerm a x τ 1 y) at hg
  have hi := logarithmicMellinTerm_integral a hx0 hτ Nat.one_ne_zero
  simp only [logarithmicMellinTerm, a, ite_eq_left rfl, Nat.cast_one, Complex.one_cpow,
    one_mul] at hg hi
  have hm : mellinWeightTwo ((1 : ℝ) / x) = (Real.log x : ℂ) := by
    have ht : (1 : ℝ) / x ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨div_pos zero_lt_one hx0, (div_lt_one hx0).mpr hx |>.le⟩
    rw [mellinWeightTwo, Set.indicator_of_mem ht, one_div, Real.log_inv, Complex.ofReal_neg,
      neg_neg]
  rw [hm] at hi
  exact ⟨hg, hi.symm⟩

end PseudoPrime.AnalyticNumberTheory.General
