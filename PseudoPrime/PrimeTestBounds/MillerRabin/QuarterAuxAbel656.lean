/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxNumerics656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerError570
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbelInterval
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.Analysis.LogPowerTailIntegral
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevBoundary43
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.EulerDerivatives
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Centered Abel bound for the section 132 auxiliary Euler tail -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The positive quadratic envelope of the auxiliary trace polynomial,
in the logarithmic coordinate measured from the split. -/
def quarterAuxTailPoly656 (u : ℝ) : ℝ :=
  6.19661190 * u + 3.305751637 * u ^ 2

/-- The envelope for the magnitude of the slope polynomial in the
centered Abel integral. Its coefficients are nonnegative. -/
noncomputable def quarterAuxSlope656 (u : ℝ) : ℝ :=
  (8 / 5) * quarterAuxTailPoly656 u + (6.19661190 + 2 * 3.305751637 * u)

/-- The untruncated Euler density that is integrated on the half-line
starting at exp(119/10). Its value at that endpoint is zero. -/
noncomputable def quarterAuxDensity656 (t : ℝ) : ℝ :=
  t ^ (-(8 / 5) : ℝ) * quarterAuxTailPoly656 (Real.log t - 119 / 10)

/-- The lower integration endpoint lies inside the finite square-root
envelope for the Chebyshev function. -/
theorem quarter_aux_split_range_656 : Real.exp (119 / 10) ∈ Set.Icc (1423 : ℝ) 1000000 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 10) (j := 3) (n := 16) (lo := 23025 / 10000)
      (hi := 23026 / 10000) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpow (n : ℕ) : Real.log ((10 : ℝ) ^ n) = n * Real.log 10 := Real.log_pow _ _
  have h₁ : Real.log (100000 : ℝ) ≤ 119 / 10 := by
    rw [show (100000 : ℝ) = 10 ^ (5 : ℕ) by norm_num only, hpow]
    norm_num only [Nat.cast_ofNat]
    linarith only [h.2]
  have h₂ : (119 / 10 : ℝ) ≤ Real.log 1000000 := by
    rw [show (1000000 : ℝ) = 10 ^ (6 : ℕ) by norm_num only, hpow]
    norm_num only [Nat.cast_ofNat]
    linarith only [h.1]
  exact
    ⟨(by norm_num only : (1423 : ℝ) ≤ 100000).trans
        ((Real.log_le_iff_le_exp (by norm_num only)).mp h₁),
      (Real.le_log_iff_exp_le (by norm_num only)).mp h₂⟩

/-- The lower boundary term in centered Abel summation vanishes because
the shifted quadratic has no constant term. -/
theorem quarter_aux_density_split_656 : quarterAuxDensity656 (Real.exp (119 / 10)) = 0 := by
  simp only [quarterAuxDensity656, Real.log_exp, sub_self, quarterAuxTailPoly656, mul_zero,
    zero_pow (by decide : 2 ≠ 0), add_zero]

private theorem aux_poly_deriv (u : ℝ) :
    HasDerivAt quarterAuxTailPoly656 (6.19661190 + 2 * 3.305751637 * u) u := by
  convert
    ((hasDerivAt_id u).const_mul 6.19661190).add
      (((hasDerivAt_id u).pow 2).const_mul 3.305751637) using
    1
  · funext x
    simp only [quarterAuxTailPoly656, Pi.add_apply, Pi.pow_apply, id_eq]
  · norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring

private theorem aux_density_hasDeriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt quarterAuxDensity656
      (t ^ (-(8 / 5 : ℝ) - 1) *
        ((6.19661190 + 2 * 3.305751637 * (Real.log t - 119 / 10)) -
          (8 / 5) * quarterAuxTailPoly656 (Real.log t - 119 / 10)))
      t := by
  have h :=
    ((Real.hasDerivAt_rpow_const (p := -(8 / 5 : ℝ)) (Or.inl ht.ne')).mul
      ((aux_poly_deriv (Real.log t - 119 / 10)).comp t
        ((Real.hasDerivAt_log ht.ne').sub_const (119 / 10))))
  convert h using 1
  · rfl
  · simp only [Function.comp_apply]
    rw [Real.rpow_sub_one ht.ne', div_eq_mul_inv]
    ring

/-- For t above the split, the absolute slope costs at most the sum
of the two nonnegative components of the logarithmic slope polynomial. -/
theorem quarter_aux_density_slope_656 {t : ℝ} (ht : Real.exp (119 / 10) ≤ t) :
    |deriv quarterAuxDensity656 t| ≤
      t ^ (-(8 / 5 : ℝ) - 1) * quarterAuxSlope656 (Real.log t - 119 / 10) := by
  have hp := (Real.exp_pos _).trans_le ht
  have hu : 0 ≤ Real.log t - 119 / 10 := sub_nonneg.mpr ((Real.le_log_iff_exp_le hp).mpr ht)
  rw [(aux_density_hasDeriv hp).deriv, abs_mul, abs_of_nonneg (Real.rpow_nonneg hp.le _)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hp.le _)
  unfold quarterAuxSlope656
  have hQ : 0 ≤ quarterAuxTailPoly656 (Real.log t - 119 / 10) := by
    unfold quarterAuxTailPoly656
    positivity
  have hD : 0 ≤ 6.19661190 + 2 * 3.305751637 * (Real.log t - 119 / 10) := by positivity
  rw [abs_le]
  constructor <;> linarith only [hQ, hD]

private theorem aux_slope_sqrt {t : ℝ} (ht : Real.exp (119 / 10) ≤ t) :
    Real.sqrt t * |deriv quarterAuxDensity656 t| ≤
      t ^ (-(11 / 10 : ℝ) - 1) * quarterAuxSlope656 (Real.log t - 119 / 10) := by
  have hp := (Real.exp_pos _).trans_le ht
  have h := mul_le_mul_of_nonneg_left (quarter_aux_density_slope_656 ht) (Real.sqrt_nonneg t)
  refine h.trans_eq ?_
  rw [← mul_assoc, Real.sqrt_eq_rpow, ← Real.rpow_add hp]
  norm_num only

/-- The finite psi envelope bounds the absolute Abel error below one million. -/
theorem quarter_aux_error_finite_656 {t : ℝ} (ht : Real.exp (119 / 10) ≤ t) (hU : t ≤ 1000000) :
    |(Chebyshev.psi t - t) * deriv quarterAuxDensity656 t| ≤
      (4 / 5) * (t ^ (-(11 / 10 : ℝ) - 1) * quarterAuxSlope656 (Real.log t - 119 / 10)) := by
  have he :=
    AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million
      (quarter_aux_split_range_656.1.trans ht) hU
  rw [abs_mul]
  exact
    (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans
      (by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (aux_slope_sqrt ht) (by norm_num only))

/-- The RH square-root log-square envelope bounds the absolute Abel
error above one million. Both ranges use the same slope polynomial. -/
theorem quarter_aux_error_infinite_656 (hRH : RiemannHypothesis) {t : ℝ} (ht : (1000000 : ℝ) ≤ t) :
    |(Chebyshev.psi t - t) * deriv quarterAuxDensity656 t| ≤
      (Real.log t ^ 2 / 24) *
        (t ^ (-(11 / 10 : ℝ) - 1) * quarterAuxSlope656 (Real.log t - 119 / 10)) := by
  rw [abs_mul]
  apply (mul_le_mul_of_nonneg_right (euler570_psi_high hRH ht) (abs_nonneg _)).trans
  rw [mul_comm (Real.sqrt t), mul_assoc]
  exact
    mul_le_mul_of_nonneg_left (aux_slope_sqrt (quarter_aux_split_range_656.2.trans ht))
      (div_nonneg (sq_nonneg _) (by norm_num only))

/-- Multiplying a shifted log-quadratic by a logarithmic moment preserves
integrability on any upper half-line above one. -/
private theorem aux_integrable_quad {d x : ℝ} (hd : 0 < d) (hx : 1 ≤ x) (k : ℕ) (A B C T : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦
        t ^ (-d - 1) * Real.log t ^ k * (A * (Real.log t - T) ^ 2 + B * (Real.log t - T) + C))
      (Set.Ioi x) := by
  have hm := fun j ↦ Analysis.log_power_tail_integrable hd hx j
  have h :=
    (((hm (k + 2)).const_mul A).add ((hm (k + 1)).const_mul (B - 2 * A * T))).add
      ((hm k).const_mul (C - B * T + A * T ^ 2))
  apply h.congr
  exact
    Filter.Eventually.of_forall
      (fun t ↦ by
        simp only [Pi.add_apply, pow_add]
        ring)

private theorem aux_integral_quad {d x : ℝ} (hd : 0 < d) (hx : 1 ≤ x) (k : ℕ) (A B C T : ℝ) :
    (∫ t in Set.Ioi x,
        t ^ (-d - 1) * Real.log t ^ k * (A * (Real.log t - T) ^ 2 + B * (Real.log t - T) + C)) =
      x ^ (-d) *
        (A * Analysis.logPowerTailPoly d (k + 2) (Real.log x) +
          (B - 2 * A * T) * Analysis.logPowerTailPoly d (k + 1) (Real.log x) +
          (C - B * T + A * T ^ 2) * Analysis.logPowerTailPoly d k (Real.log x)) := by
  let m := fun j t ↦ Real.log t ^ j * t ^ (-d - 1)
  have hi (j : ℕ) : MeasureTheory.IntegrableOn (m j) (Set.Ioi x) :=
    Analysis.log_power_tail_integrable hd hx j
  have he (j : ℕ) :
    (∫ t in Set.Ioi x, m j t) = x ^ (-d) * Analysis.logPowerTailPoly d j (Real.log x) :=
    Analysis.log_power_tail_integral hd hx j
  let p := fun t ↦ A * m (k + 2) t + (B - 2 * A * T) * m (k + 1) t + (C - B * T + A * T ^ 2) * m k t
  have h (t : ℝ) :
    t ^ (-d - 1) * Real.log t ^ k * (A * (Real.log t - T) ^ 2 + B * (Real.log t - T) + C) =
      p t := by
    dsimp only [p, m]
    rw [pow_add, pow_add, pow_one]
    ring
  simp only [h, p]
  have hA := (hi (k + 2)).const_mul A
  have hB := (hi (k + 1)).const_mul (B - 2 * A * T)
  have hC := (hi k).const_mul (C - B * T + A * T ^ 2)
  have h₁ := MeasureTheory.integral_add (hA.add hB) hC
  have h₂ := MeasureTheory.integral_add hA hB
  simp only [Pi.add_apply] at h₁ h₂
  rw [h₁, h₂]
  simp only [MeasureTheory.integral_const_mul, he]
  ring

/-- The finite square-root psi envelope times the absolute slope bound. -/
noncomputable def quarterAuxFiniteMajor656 (t : ℝ) : ℝ :=
  (4 / 5) * (t ^ (-(11 / 10 : ℝ) - 1) * quarterAuxSlope656 (Real.log t - 119 / 10))

/-- The RH square-root log-square envelope times the absolute slope bound. -/
noncomputable def quarterAuxHighMajor656 (t : ℝ) : ℝ :=
  (Real.log t ^ 2 / 24) * (t ^ (-(11 / 10 : ℝ) - 1) * quarterAuxSlope656 (Real.log t - 119 / 10))

private theorem aux_low_integrable {x : ℝ} (hx : 1 ≤ x) :
    MeasureTheory.IntegrableOn quarterAuxFiniteMajor656 (Set.Ioi x) := by
  have h :=
    (aux_integrable_quad (d := 11 / 10) (by norm_num only) hx 0 (8 / 5 * 3.305751637)
          (8 / 5 * 6.19661190 + 2 * 3.305751637) 6.19661190 (119 / 10)).const_mul
      (4 / 5)
  apply h.congr
  exact
    Filter.Eventually.of_forall
      (fun t ↦ by
        dsimp only [quarterAuxFiniteMajor656, quarterAuxSlope656, quarterAuxTailPoly656]
        ring)

private theorem aux_high_integrable {x : ℝ} (hx : 1 ≤ x) :
    MeasureTheory.IntegrableOn quarterAuxHighMajor656 (Set.Ioi x) := by
  have h :=
    (aux_integrable_quad (d := 11 / 10) (by norm_num only) hx 2 (8 / 5 * 3.305751637)
          (8 / 5 * 6.19661190 + 2 * 3.305751637) 6.19661190 (119 / 10)).const_mul
      (1 / 24)
  apply h.congr
  exact
    Filter.Eventually.of_forall
      (fun t ↦ by
        dsimp only [quarterAuxHighMajor656, quarterAuxSlope656, quarterAuxTailPoly656]
        ring)

private theorem aux_low_nonneg {t : ℝ} (ht : Real.exp (119 / 10) ≤ t) :
    0 ≤ quarterAuxFiniteMajor656 t := by
  have hp := (Real.exp_pos _).trans_le ht
  have hu := sub_nonneg.mpr ((Real.le_log_iff_exp_le hp).mpr ht)
  unfold quarterAuxFiniteMajor656 quarterAuxSlope656 quarterAuxTailPoly656
  positivity

private theorem aux_density_integrable {x : ℝ} (hx : 1 ≤ x) :
    MeasureTheory.IntegrableOn quarterAuxDensity656 (Set.Ioi x) := by
  apply
    (aux_integrable_quad (d := 3 / 5) (by norm_num only) hx 0 3.305751637 6.19661190 0
        (119 / 10)).congr
  exact
    Filter.Eventually.of_forall
      (fun t ↦ by
        simp only [quarterAuxDensity656, quarterAuxTailPoly656, pow_zero, mul_one, add_zero,
          show -(3 / 5 : ℝ) - 1 = -(8 / 5) by norm_num only]
        ring)

private theorem aux_density_boundary :
    Filter.Tendsto (fun t : ℝ ↦ (Chebyshev.psi t - t) * quarterAuxDensity656 t) Filter.atTop
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
  let A : ℝ := 3.305751637
  let B : ℝ := 6.19661190
  let T : ℝ := 119 / 10
  have h :=
    (((hm 2).const_mul (4 * A)).add ((hm 1).const_mul (4 * (B - 2 * A * T)))).add
      ((hm 0).const_mul (4 * (A * T ^ 2 - B * T)))
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  exact
    Filter.Eventually.of_forall
      (fun t ↦ by
        simp only [E, A, B, T, quarterAuxDensity656, quarterAuxTailPoly656,
          AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight, pow_zero, pow_one]
        ring)

private theorem aux_density_summable :
    Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterAuxDensity656 n) := by
  have hm :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 8 / 5)
      (by norm_num only)
  let A : ℝ := 3.305751637
  let B : ℝ := 6.19661190
  let T : ℝ := 119 / 10
  apply
    (((hm 2).mul_left A).add ((hm 1).mul_left (B - 2 * A * T))).add
        ((hm 0).mul_left (A * T ^ 2 - B * T)) |>.congr
  intro n
  simp only [quarterAuxDensity656, quarterAuxTailPoly656, Real.rpow_neg (Nat.cast_nonneg n),
    pow_zero, pow_one, A, B, T, div_eq_mul_inv]
  ring

private theorem aux_error_major (hRH : RiemannHypothesis) {t : ℝ} (ht : Real.exp (119 / 10) < t) :
    ‖(Chebyshev.psi t - t) * deriv quarterAuxDensity656 t‖ ≤
      quarterAuxFiniteMajor656 t + (Set.Ioi (1000000 : ℝ)).indicator quarterAuxHighMajor656 t := by
  rw [Real.norm_eq_abs]
  by_cases hU : 1000000 < t
  · rw [Set.indicator_of_mem (show t ∈ Set.Ioi (1000000 : ℝ) from hU)]
    exact
      (quarter_aux_error_infinite_656 hRH hU.le).trans
        (le_add_of_nonneg_left (aux_low_nonneg ht.le))
  · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (1000000 : ℝ) from hU), add_zero]
    exact quarter_aux_error_finite_656 ht.le (le_of_not_gt hU)

/-- Centered Abel summation bounds the positive tail by three integrals.
The boundary at exp(119/10) vanishes, and the high error starts at one million. -/
theorem quarter_aux_abel_bound_656 (hRH : RiemannHypothesis) :
    let a := Real.exp (119 / 10)
    let f := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterAuxDensity656 n
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n ≤
      (∫ t in Set.Ioi a, quarterAuxDensity656 t) + (∫ t in Set.Ioi a, quarterAuxFiniteMajor656 t) +
        (∫ t in Set.Ioi 1000000, quarterAuxHighMajor656 t) := by
  intro a f
  let E := fun t : ℝ ↦ (Chebyshev.psi t - t) * deriv quarterAuxDensity656 t
  have ha : 0 < a := Real.exp_pos _
  have ha₁ : 1 ≤ a := Real.one_le_exp (by norm_num only)
  have hlow := aux_low_integrable ha₁
  have hhigh :
    MeasureTheory.IntegrableOn ((Set.Ioi (1000000 : ℝ)).indicator quarterAuxHighMajor656)
      (Set.Ioi a) := by
    apply (MeasureTheory.integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet).mpr
    exact (aux_high_integrable (by norm_num only)).mono_set Set.inter_subset_left
  have hmaj :
    ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioi a),
      ‖E t‖ ≤
        quarterAuxFiniteMajor656 t +
          (Set.Ioi (1000000 : ℝ)).indicator quarterAuxHighMajor656 t := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact aux_error_major hRH ht
  have hiE : MeasureTheory.IntegrableOn E (Set.Ioi a) :=
    (hlow.add hhigh).mono'
      (((Chebyshev.psi_mono.measurable.sub measurable_id).mul
          (measurable_deriv quarterAuxDensity656)).aestronglyMeasurable)
      hmaj
  have he := MeasureTheory.norm_integral_le_of_norm_le (hlow.add hhigh) hmaj
  rw [Real.norm_eq_abs] at he
  change
    _ ≤
      ∫ t in Set.Ioi a,
        quarterAuxFiniteMajor656 t +
          (Set.Ioi (1000000 : ℝ)).indicator quarterAuxHighMajor656 t at he
  rw [MeasureTheory.integral_add hlow hhigh, MeasureTheory.setIntegral_indicator measurableSet_Ioi,
    Set.Ioi_inter_Ioi, max_eq_right quarter_aux_split_range_656.2] at he
  have hd : ContinuousOn (deriv quarterAuxDensity656) (Set.Ioi (0 : ℝ)) := by
    refine ContinuousOn.congr ?_ (fun t ht ↦ (aux_density_hasDeriv ht).deriv)
    intro t ht
    have hp : 0 < t := ht
    have hlog : ContinuousAt Real.log t := Real.continuousAt_log hp.ne'
    have hpol :
      ContinuousAt
        (fun u : ℝ ↦
          6.19661190 + 2 * 3.305751637 * (Real.log u - 119 / 10) -
            (8 / 5) * quarterAuxTailPoly656 (Real.log u - 119 / 10))
        t := by
      unfold quarterAuxTailPoly656
      fun_prop
    exact ((Real.continuousAt_rpow_const t _ (Or.inl hp.ne')).mul hpol).continuousWithinAt
  have hab :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_integral ha.le
      (fun b _ t ht ↦ (aux_density_hasDeriv (ha.trans_le ht.1)).differentiableAt)
      (fun b _ ↦ (hd.mono (fun {_} (ht : _ ∈ Set.Icc a b) ↦ ha.trans_le ht.1)).integrableOn_Icc)
      (aux_density_integrable ha₁) hiE aux_density_boundary aux_density_summable
  change _ = _ - (Chebyshev.psi a - a) * quarterAuxDensity656 a - ∫ t in Set.Ioi a, E t at hab
  rw [show quarterAuxDensity656 a = 0 from quarter_aux_density_split_656, mul_zero, sub_zero] at hab
  linarith only [hab, (abs_le.mp he).1]

/-- The closed logarithmic cutoff has the same sum as the open Abel
cutoff because the weight vanishes at equality. -/
private theorem aux_density_cutoff_eq :
    let a := Real.exp (119 / 10)
    let f := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterAuxDensity656 n
    (∑' n : ℕ, if (119 / 10 : ℝ) ≤ Real.log n then f n else 0) =
      (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n := by
  intro a f
  have h := aux_density_summable.sum_add_tsum_compl (s := Finset.Ioc 0 ⌊a⌋₊)
  change
    (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n) + (∑' n : { n : ℕ // n ∉ Finset.Ioc 0 ⌊a⌋₊ }, f n) =
      (∑' n, f n) at h
  have he := tsum_subtype {n : ℕ | n ∉ Finset.Ioc 0 ⌊a⌋₊} f
  refine (tsum_congr ?_).trans (he.symm.trans (eq_sub_of_add_eq' h))
  intro n
  by_cases h₀ : n = 0
  · simp only [h₀, f, ArithmeticFunction.map_zero, zero_mul, ite_self, Set.indicator_apply]
  have hp : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h₀)
  have ha : 0 ≤ a := (Real.exp_pos _).le
  by_cases hn : n ≤ ⌊a⌋₊
  · have hm : n ∈ Finset.Ioc 0 ⌊a⌋₊ := Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h₀, hn⟩
    have hlog := (Real.log_le_iff_le_exp hp).mpr ((Nat.le_floor_iff ha).mp hn)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hm, not_true_eq_false, ite_false]
    split
    · have he := le_antisymm hlog ‹_›
      simp only [f, quarterAuxDensity656, he, sub_self, quarterAuxTailPoly656, mul_zero,
        zero_pow (by decide : 2 ≠ 0), add_zero]
    · exact rfl
  have haN := (Nat.floor_lt ha).mp (lt_of_not_ge hn)
  have hlog := (Real.lt_log_iff_exp_lt hp).mpr haN
  have hm : n ∉ Finset.Ioc 0 ⌊a⌋₊ := fun h ↦ hn (Finset.mem_Ioc.mp h).2
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, hm, hlog.le, not_false_eq_true, ite_true]

/-- Under RH the auxiliary trace series on either of the section 132
intervals costs at most four times the three Abel integrals. -/
theorem quarter_aux_trace_abel_656 (hRH : RiemannHypothesis) {X : ℝ} (hX : (322 : ℝ) ^ 2 ≤ X)
    (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4) :
    let a := Real.exp (119 / 10)
    (∑' n : ℕ,
        if X < (n : ℝ) then
          α n * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ)) *
            quarterAuxPoly656 (Real.log n)
        else 0) ≤
      4 *
        ((∫ t in Set.Ioi a, quarterAuxDensity656 t) +
          (∫ t in Set.Ioi a, quarterAuxFiniteMajor656 t) +
          (∫ t in Set.Ioi 1000000, quarterAuxHighMajor656 t)) := by
  intro a
  apply (quarter_aux_euler_tail_656 hX α hα).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  have he := aux_density_cutoff_eq
  dsimp only at he
  simp only [quarterAuxDensity656, quarterAuxTailPoly656, Real.rpow_neg (Nat.cast_nonneg _),
    div_eq_mul_inv, mul_assoc] at he ⊢
  rw [he]
  simpa only [quarterAuxDensity656, quarterAuxTailPoly656, Real.rpow_neg (Nat.cast_nonneg _),
    div_eq_mul_inv, mul_assoc, a] using quarter_aux_abel_bound_656 hRH

/-- The main Abel integral is the sum of the first two shifted exponential
moments at decay rate 3/5. -/
theorem quarter_aux_main_integral_656 :
    (∫ t in Set.Ioi (Real.exp (119 / 10)), quarterAuxDensity656 t) =
      Real.exp (-(357 / 50 : ℝ)) * (6.19661190 / (3 / 5) ^ 2 + 2 * 3.305751637 / (3 / 5) ^ 3) := by
  have ha : 1 ≤ Real.exp (119 / 10 : ℝ) := Real.one_le_exp (by norm_num only)
  have h :=
    aux_integral_quad (d := 3 / 5) (by norm_num only) ha 0 3.305751637 6.19661190 0 (119 / 10)
  simp only [Real.log_exp, pow_zero, mul_one, zero_add, add_zero,
    show -(3 / 5 : ℝ) - 1 = -(8 / 5) by norm_num only] at h
  have h₁ : (Real.exp (119 / 10)) ^ (-(3 / 5 : ℝ)) = Real.exp (-(357 / 50 : ℝ)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    norm_num only
  rw [h₁] at h
  unfold quarterAuxDensity656 quarterAuxTailPoly656
  simp_rw [add_comm ((6.19661190 : ℝ) * _)]
  rw [h]
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat]

/-- The finite-envelope integral is the sum of three shifted exponential
moments at decay rate 11/10. -/
theorem quarter_aux_finite_integral_656 :
    (∫ t in Set.Ioi (Real.exp (119 / 10)), quarterAuxFiniteMajor656 t) =
      (4 / 5) * Real.exp (-(1309 / 100 : ℝ)) *
        (6.19661190 / (11 / 10) + ((8 / 5) * 6.19661190 + 2 * 3.305751637) / (11 / 10) ^ 2 +
          2 * (8 / 5) * 3.305751637 / (11 / 10) ^ 3) := by
  have ha : 1 ≤ Real.exp (119 / 10 : ℝ) := Real.one_le_exp (by norm_num only)
  have h :=
    aux_integral_quad (d := 11 / 10) (by norm_num only) ha 0 (8 / 5 * 3.305751637)
      (8 / 5 * 6.19661190 + 2 * 3.305751637) 6.19661190 (119 / 10)
  simp only [Real.log_exp, pow_zero, mul_one, zero_add] at h
  have h₁ : (Real.exp (119 / 10)) ^ (-(11 / 10 : ℝ)) = Real.exp (-(1309 / 100 : ℝ)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    norm_num only
  rw [h₁] at h
  unfold quarterAuxFiniteMajor656
  rw [MeasureTheory.integral_const_mul]
  have he (t : ℝ) :
    quarterAuxSlope656 (Real.log t - 119 / 10) =
      (8 / 5 * 3.305751637) * (Real.log t - 119 / 10) ^ 2 +
        (8 / 5 * 6.19661190 + 2 * 3.305751637) * (Real.log t - 119 / 10) +
        6.19661190 := by
    unfold quarterAuxSlope656 quarterAuxTailPoly656
    ring
  simp only [he]
  rw [h]
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat]
  ring

/-- The high-envelope integral expands into moments of degrees two through four. -/
theorem quarter_aux_high_integral_656 :
    let v := Real.log 1000000
    (∫ t in Set.Ioi 1000000, quarterAuxHighMajor656 t) =
      (1000000 : ℝ) ^ (-(11 / 10) : ℝ) / 24 *
        (5.2892026192 * Analysis.logPowerTailPoly (11 / 10) 4 v -
            109.35694002296 * Analysis.logPowerTailPoly (11 / 10) 3 v +
          558.540215268312 * Analysis.logPowerTailPoly (11 / 10) 2 v) := by
  intro v
  have h :=
    aux_integral_quad (d := 11 / 10) (x := 1000000) (by norm_num only) (by norm_num only) 2
      (8 / 5 * 3.305751637) (8 / 5 * 6.19661190 + 2 * 3.305751637) 6.19661190 (119 / 10)
  have he (t : ℝ) :
    quarterAuxHighMajor656 t =
      (1 / 24) *
        (t ^ (-(11 / 10 : ℝ) - 1) * Real.log t ^ 2 *
          ((8 / 5 * 3.305751637) * (Real.log t - 119 / 10) ^ 2 +
            (8 / 5 * 6.19661190 + 2 * 3.305751637) * (Real.log t - 119 / 10) +
            6.19661190)) := by
    unfold quarterAuxHighMajor656 quarterAuxSlope656 quarterAuxTailPoly656
    ring
  simp only [he, MeasureTheory.integral_const_mul, h, Nat.reduceAdd, v]
  ring

private theorem aux_exp_neg_upper {x u : ℝ} (hx : 0 ≤ x) (hu : 0 < u)
    (h : 1 / u ≤ ∑ j ∈ Finset.range 42, x ^ j / (j.factorial : ℝ)) : Real.exp (-x) ≤ u := by
  have he :=
    one_div_le_one_div_of_le (one_div_pos.mpr hu) (h.trans (Real.sum_le_exp_of_nonneg hx 42))
  simpa only [one_div, inv_inv, Real.exp_neg] using he

private theorem aux_main_integral_bound :
    (∫ t in Set.Ioi (Real.exp (119 / 10)), quarterAuxDensity656 t) ≤ 0.0379106914 := by
  rw [quarter_aux_main_integral_656]
  have h :=
    aux_exp_neg_upper (x := 357 / 50) (u := 0.000792752097) (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  linarith only [h]

private theorem aux_finite_integral_bound :
    (∫ t in Set.Ioi (Real.exp (119 / 10)), quarterAuxFiniteMajor656 t) ≤ 0.00004501581 := by
  rw [quarter_aux_finite_integral_656]
  have h :=
    aux_exp_neg_upper (x := 1309 / 100) (u := 0.000002065785535) (by norm_num only)
      (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  linarith only [h]

private theorem aux_high_integral_bound :
    (∫ t in Set.Ioi 1000000, quarterAuxHighMajor656 t) ≤ 0.000219845 := by
  rw [quarter_aux_high_integral_656]
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 10) (j := 3) (n := 16) (lo :=
      230258509 / 100000000) (hi := 230258510 / 100000000) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl
  have hlog : Real.log 1000000 = 6 * Real.log 10 := by
    rw [show (1000000 : ℝ) = (10 : ℝ) ^ 6 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hlo : 13.81551054 ≤ Real.log 1000000 := by
    rw [hlog]; linarith only [hl.1]
  have hhi : Real.log 1000000 ≤ 13.81551060 := by
    rw [hlog]; linarith only [hl.2]
  have hm {z u : ℝ} (h₀ : 0 ≤ z) (h₁ : z ≤ u) (k : ℕ) :=
    Analysis.log_power_tail_poly_mono (by norm_num only : (0 : ℝ) < 11 / 10) h₀ h₁ k
  have ha := hm (by linarith only [hlo]) hhi 4
  have hb := hm (by norm_num only) hlo 3
  have hc := hm (by linarith only [hlo]) hhi 2
  have hB :
    5.2892026192 * Analysis.logPowerTailPoly (11 / 10) 4 (Real.log 1000000) -
          109.35694002296 * Analysis.logPowerTailPoly (11 / 10) 3 (Real.log 1000000) +
        558.540215268312 * Analysis.logPowerTailPoly (11 / 10) 2 (Real.log 1000000) ≤
      21005.22 := by
    norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat] at ha hb hc ⊢
    linarith only [ha, hb, hc]
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1000000) (p := 11) (d :=
        10) (lo := 0) (hi := 251188644 / 10 ^ 15) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hp
  exact
    ((mul_le_mul_of_nonneg_left hB (by positivity)).trans
          (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hp (by norm_num only))
            (by norm_num only))).trans
      (by norm_num only)

/-- Under RH the same numerical upper bound for the auxiliary Euler trace
applies to both section 132 intervals. The factor four is the trace range. -/
theorem quarter_aux_trace_cap_656 (hRH : RiemannHypothesis) {X : ℝ} (hX : (322 : ℝ) ^ 2 ≤ X)
    (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4) :
    (∑' n : ℕ,
        if X < (n : ℝ) then
          α n * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ)) *
            quarterAuxPoly656 (Real.log n)
        else 0) ≤
      4 * 0.038175553 := by
  have h := quarter_aux_trace_abel_656 hRH hX α hα
  dsimp only at h
  linarith only [h, aux_main_integral_bound, aux_finite_integral_bound, aux_high_integral_bound]

end PseudoPrime.PrimeTestBounds.MillerRabin
