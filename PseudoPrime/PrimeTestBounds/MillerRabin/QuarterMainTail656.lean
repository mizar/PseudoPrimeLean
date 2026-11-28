/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerMoments570
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbelInterval
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerError570
import PseudoPrime.AnalyticNumberTheory.Arithmetic.NaturalTailLimit
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInterval600

/-! # Direct Abel tail for the section 132 Euler density -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The real-variable Euler weight at exponent 8/5. Its values at natural
indices enter the Mangoldt sum, and its derivative controls the Abel remainder. -/
noncomputable def eulerDensity656 (t : ℝ) : ℝ :=
  t ^ (-(8 / 5 : ℝ)) * (3 / 8 + 33 / 80 * Real.log t + 121 / 800 * Real.log t ^ 2)

/-- The derivative of the section 132 weight, written as a negative power times a
quadratic in the logarithm to permit termwise integration of its absolute value. -/
noncomputable def eulerSlope656 (t : ℝ) : ℝ :=
  -(t ^ (-(13 / 5 : ℝ))) * (3 / 16 + 143 / 400 * Real.log t + 121 / 500 * Real.log t ^ 2)

/-- At positive arguments the product and chain rules give the explicit Euler slope. -/
theorem eulerDensity656_deriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt eulerDensity656 (eulerSlope656 t) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have hd :=
    (Real.hasDerivAt_rpow_const (p := -(8 / 5 : ℝ)) (Or.inl ht.ne')).mul
      (((hasDerivAt_const t (3 / 8 : ℝ)).add (hl.const_mul (33 / 80))).add
        ((hl.pow 2).const_mul (121 / 800)))
  apply hd.congr_deriv
  have hp : t ^ (-(13 / 5 : ℝ)) = t ^ (-(8 / 5 : ℝ)) / t := by
    rw [show -(13 / 5 : ℝ) = -(8 / 5 : ℝ) - 1 by norm_num only, Real.rpow_sub ht, Real.rpow_one]
  unfold eulerSlope656
  rw [show -(8 / 5 : ℝ) - 1 = -(13 / 5 : ℝ) by norm_num only, hp]
  simp only [Pi.add_apply, Pi.pow_apply]
  ring

/-- On a positive finite interval the Euler sum minus its main integral equals
the centered boundary difference minus the integral of the psi error against
the explicit slope. This specializes centered Abel summation to the section 132 tail. -/
theorem euler656_abel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * eulerDensity656 n) -
        (∫ t : ℝ in a..b, eulerDensity656 t) =
      (Chebyshev.psi b - b) * eulerDensity656 b - (Chebyshev.psi a - a) * eulerDensity656 a -
        ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * eulerSlope656 t := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) := eulerDensity656_deriv (ha.trans_le ht.1)
  have hc : ContinuousOn eulerSlope656 (Set.Icc a b) := by
    intro t ht
    have hp := (ha.trans_le ht.1).ne'
    have hl := Real.continuousAt_log hp
    exact
      ((Real.continuousAt_rpow_const t _ (Or.inl hp)).neg.mul
          ((continuousAt_const.add (continuousAt_const.mul hl)).add
            (continuousAt_const.mul (hl.pow 2)))).continuousWithinAt
  have he : Set.EqOn (deriv eulerDensity656) eulerSlope656 (Set.Icc a b) := fun t ht ↦
    (hd t ht).deriv
  have hi : MeasureTheory.IntegrableOn (deriv eulerDensity656) (Set.Icc a b) :=
    (hc.congr he).integrableOn_Icc
  have h :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_interval ha.le hab
      (fun t ht ↦ (hd t ht).differentiableAt) hi
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  exact congrArg ((Chebyshev.psi t - t) * ·) (he ht)

/-- Above one, the logarithm is nonnegative and every coefficient in the quadratic
factor is positive, so the derivative of the Euler weight is nonpositive. -/
theorem eulerSlope656_nonpos {t : ℝ} (ht : 1 ≤ t) : eulerSlope656 t ≤ 0 := by
  have hp := zero_le_one.trans ht
  have hl := Real.log_nonneg ht
  unfold eulerSlope656
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.rpow_nonneg hp _)) (by positivity)

/-- For a continuous majorant of the psi error on a positive interval above one,
bound the centered Abel integral by integrating the majorant against the negative slope. -/
theorem euler656_error_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) {B : ℝ → ℝ}
    (hc : ContinuousOn B (Set.Icc a b)) (he : ∀ t ∈ Set.Icc a b, |Chebyshev.psi t - t| ≤ B t) :
    |∫ t : ℝ in a..b, (Chebyshev.psi t - t) * eulerSlope656 t| ≤
      ∫ t : ℝ in a..b, B t * -eulerSlope656 t := by
  have hs : ContinuousOn eulerSlope656 (Set.Icc a b) := by
    intro t ht
    have hp := (zero_lt_one.trans_le (ha.trans ht.1)).ne'
    have hl := Real.continuousAt_log hp
    exact
      ((Real.continuousAt_rpow_const t _ (Or.inl hp)).neg.mul
          ((continuousAt_const.add (continuousAt_const.mul hl)).add
            (continuousAt_const.mul (hl.pow 2)))).continuousWithinAt
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab, ← Real.norm_eq_abs]
  apply
    MeasureTheory.norm_integral_le_of_norm_le
      ((hc.mul hs.neg).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  have h := he t ⟨ht.1.le, ht.2⟩
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (eulerSlope656_nonpos (ha.trans ht.1.le))]
  exact mul_le_mul_of_nonneg_right h (neg_nonneg.mpr (eulerSlope656_nonpos (ha.trans ht.1.le)))

/-- From 1423 through one million, the finite psi certificate bounds the Euler
remainder integral by the four-fifths square-root integral. -/
theorem euler656_error_million {a b : ℝ} (ha : 1423 ≤ a) (hab : a ≤ b) (hb : b ≤ 1000000) :
    |∫ t : ℝ in a..b, (Chebyshev.psi t - t) * eulerSlope656 t| ≤
      ∫ t : ℝ in a..b, (4 / 5 : ℝ) * Real.sqrt t * -eulerSlope656 t := by
  apply
    euler656_error_integral (by linarith only [ha]) hab
      (continuousOn_const.mul Real.continuous_sqrt.continuousOn)
  exact fun t ht ↦
    AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million (ha.trans ht.1) (ht.2.trans hb)

/-- On finite intervals above one million, RH bounds the centered Euler remainder
by the explicit log-square integral needed for the section 132 tail. -/
theorem euler656_error_high (hRH : RiemannHypothesis) {a b : ℝ} (ha : 1000000 ≤ a) (hab : a ≤ b) :
    |∫ t : ℝ in a..b, (Chebyshev.psi t - t) * eulerSlope656 t| ≤
      ∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -eulerSlope656 t := by
  apply euler656_error_integral (by linarith only [ha]) hab
  · intro t ht
    have hp : 0 < t := by linarith only [ha, ht.1]
    exact
      (Real.continuous_sqrt.continuousAt.mul
          (((Real.continuousAt_log hp.ne').pow 2).div_const 24)).continuousWithinAt
  · exact fun t ht ↦ euler570_psi_high hRH (ha.trans ht.1)

/-- The Euler density has a summable Mangoldt-weighted series. -/
theorem euler_density_summable_656 :
    Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * eulerDensity656 n) := by
  have h0 :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 8 / 5)
      (by norm_num only) 0
  have h1 :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 8 / 5)
      (by norm_num only) 1
  have h2 :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 8 / 5)
      (by norm_num only) 2
  have hs :=
    (((h0.mul_left 3).add (h1.mul_left (33 / 10))).add (h2.mul_left (121 / 100))).mul_left
      (1 / 8 : ℝ)
  apply hs.congr
  intro n
  simp only [eulerDensity656, pow_zero, pow_one]
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  ring

/-- Evaluate the main Euler integral on an interval above one at decay exponent 3/5. -/
theorem euler656_main_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, eulerDensity656 t) =
      ∑ j : Fin 3,
        ![(3 / 8 : ℝ), 33 / 80, 121 / 800] j *
          (eulerMomentValue570 (3 / 5) j.val a - eulerMomentValue570 (3 / 5) j.val b) := by
  apply euler570_polynomial_interval (k := 0) (by norm_num only) ha hab
  intro t ht
  rw [Fin.sum_univ_three]
  change
    _ =
      3 / 8 * eulerMoment570 _ 0 t + 33 / 80 * eulerMoment570 _ 1 t +
        121 / 800 * eulerMoment570 _ 2 t
  unfold eulerMoment570 eulerDensity656
  rw [show -(3 / 5 : ℝ) - 1 = -(8 / 5 : ℝ) by norm_num only]
  ring

/-- Evaluate the four-fifths square-root error integral via moments of degrees zero to two. -/
theorem euler656_low_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, (4 / 5 : ℝ) * Real.sqrt t * -eulerSlope656 t) =
      ∑ j : Fin 3,
        ![(4 / 5 : ℝ) * (3 / 16), (4 / 5 : ℝ) * (143 / 400), (4 / 5 : ℝ) * (121 / 500)] j *
          (eulerMomentValue570 (11 / 10) (0 + j.val) a -
            eulerMomentValue570 (11 / 10) (0 + j.val) b) := by
  apply euler570_polynomial_interval (by norm_num only) ha hab
  intro t ht
  have hp : 0 < t := zero_lt_one.trans_le (ha.trans ht.1)
  have he : Real.sqrt t * t ^ (-(13 / 5 : ℝ)) = t ^ (-(11 / 10 : ℝ) - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
    norm_num only
  rw [Fin.sum_univ_three]
  change
    _ =
      (4 / 5 : ℝ) * (3 / 16) * eulerMoment570 _ 0 t +
        (4 / 5 : ℝ) * (143 / 400) * eulerMoment570 _ 1 t +
        (4 / 5 : ℝ) * (121 / 500) * eulerMoment570 _ 2 t
  unfold eulerSlope656 eulerMoment570
  rw [← he]
  ring

/-- Evaluate the RH log-square error integral via moments of degrees two to four. -/
theorem euler656_high_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -eulerSlope656 t) =
      ∑ j : Fin 3,
        ![(1 / 24 : ℝ) * (3 / 16), (1 / 24 : ℝ) * (143 / 400), (1 / 24 : ℝ) * (121 / 500)] j *
          (eulerMomentValue570 (11 / 10) (2 + j.val) a -
            eulerMomentValue570 (11 / 10) (2 + j.val) b) := by
  apply euler570_polynomial_interval (by norm_num only) ha hab
  intro t ht
  have hp : 0 < t := zero_lt_one.trans_le (ha.trans ht.1)
  have he : Real.sqrt t * t ^ (-(13 / 5 : ℝ)) = t ^ (-(11 / 10 : ℝ) - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
    norm_num only
  rw [Fin.sum_univ_three]
  change
    _ =
      (1 / 24 : ℝ) * (3 / 16) * eulerMoment570 _ 2 t +
        (1 / 24 : ℝ) * (143 / 400) * eulerMoment570 _ 3 t +
        (1 / 24 : ℝ) * (121 / 500) * eulerMoment570 _ 4 t
  unfold eulerSlope656 eulerMoment570
  rw [← he]
  ring

/-- The endpoint expression for the main integral, formed from its three logarithmic moments. -/
noncomputable def eulerMainTail656 (x : ℝ) : ℝ :=
  3 / 8 * eulerMomentValue570 (3 / 5) 0 x + 33 / 80 * eulerMomentValue570 (3 / 5) 1 x +
    121 / 800 * eulerMomentValue570 (3 / 5) 2 x

/-- Subtract the two main endpoint expressions to obtain the exact main integral. -/
private theorem mainDiff {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, eulerDensity656 t) = eulerMainTail656 a - eulerMainTail656 b := by
  rw [euler656_main_interval ha hab, Fin.sum_univ_three]
  unfold eulerMainTail656
  change
    (3 / 8 : ℝ) * (eulerMomentValue570 (3 / 5) 0 a - eulerMomentValue570 (3 / 5) 0 b) +
        (33 / 80 : ℝ) * (eulerMomentValue570 (3 / 5) 1 a - eulerMomentValue570 (3 / 5) 1 b) +
        (121 / 800 : ℝ) * (eulerMomentValue570 (3 / 5) 2 a - eulerMomentValue570 (3 / 5) 2 b) =
      _
  ring

/-- The endpoint expression for the finite square-root error envelope. -/
noncomputable def eulerLowError656 (x : ℝ) : ℝ :=
  3 / 20 * eulerMomentValue570 (11 / 10) 0 x + 143 / 500 * eulerMomentValue570 (11 / 10) 1 x +
    121 / 625 * eulerMomentValue570 (11 / 10) 2 x

/-- Subtract the finite-error endpoint expressions to evaluate the low error integral. -/
private theorem lowDiff {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, (4 / 5 : ℝ) * Real.sqrt t * -eulerSlope656 t) =
      eulerLowError656 a - eulerLowError656 b := by
  rw [euler656_low_interval ha hab, Fin.sum_univ_three]
  unfold eulerLowError656
  change
    ((4 / 5 : ℝ) * (3 / 16)) *
          (eulerMomentValue570 (11 / 10) 0 a - eulerMomentValue570 (11 / 10) 0 b) +
        ((4 / 5 : ℝ) * (143 / 400)) *
          (eulerMomentValue570 (11 / 10) 1 a - eulerMomentValue570 (11 / 10) 1 b) +
        ((4 / 5 : ℝ) * (121 / 500)) *
          (eulerMomentValue570 (11 / 10) 2 a - eulerMomentValue570 (11 / 10) 2 b) =
      _
  ring

/-- The endpoint expression for the RH logarithmic error envelope. -/
noncomputable def eulerHighError656 (x : ℝ) : ℝ :=
  1 / 128 * eulerMomentValue570 (11 / 10) 2 x + 143 / 9600 * eulerMomentValue570 (11 / 10) 3 x +
    121 / 12000 * eulerMomentValue570 (11 / 10) 4 x

/-- Subtract the RH-error endpoint expressions to evaluate the high error integral. -/
private theorem highDiff {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -eulerSlope656 t) =
      eulerHighError656 a - eulerHighError656 b := by
  rw [euler656_high_interval ha hab, Fin.sum_univ_three]
  unfold eulerHighError656
  change
    ((1 / 24 : ℝ) * (3 / 16)) *
          (eulerMomentValue570 (11 / 10) 2 a - eulerMomentValue570 (11 / 10) 2 b) +
        ((1 / 24 : ℝ) * (143 / 400)) *
          (eulerMomentValue570 (11 / 10) 3 a - eulerMomentValue570 (11 / 10) 3 b) +
        ((1 / 24 : ℝ) * (121 / 500)) *
          (eulerMomentValue570 (11 / 10) 4 a - eulerMomentValue570 (11 / 10) 4 b) =
      _
  ring

/-- Endpoint moments are nonnegative above one by positivity of the tail polynomial. -/
private theorem moment_nonneg {d x : ℝ} (hd : 0 < d) (hx : 1 ≤ x) (k : ℕ) :
    0 ≤ eulerMomentValue570 d k x := by
  exact
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _)
      (Analysis.log_power_tail_poly_nonneg hd (Real.log_nonneg hx) k)

/-- The Euler tail envelope retaining the exact lower Abel boundary.
The remaining moments bound the main integral and the two error integrals. -/
noncomputable def signedTail656 (x : ℝ) : ℝ :=
  eulerMainTail656 x - (Chebyshev.psi x - x) * eulerDensity656 x + eulerLowError656 x +
    eulerHighError656 1000000

/-- Centered Abel summation on both sides of one million gives a finite upper bound
with the upper psi boundary retained for the infinite limit. -/
private theorem finite_tail_upper (hRH : RiemannHypothesis) {a b : ℝ} (ha : 2701 ≤ a)
    (hav : a ≤ 1000000) (hb : 1000000 ≤ b) :
    let w := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * eulerDensity656 n
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, w n) ≤
      signedTail656 a + (Chebyshev.psi b - b) * eulerDensity656 b := by
  intro w
  have ha1 : 1 ≤ a := by linarith only [ha]
  have lo := euler656_abel (zero_lt_one.trans_le ha1) hav
  have hi := euler656_abel (by norm_num only) hb
  have el := (abs_le.mp (euler656_error_million (by linarith only [ha]) hav (le_refl 1000000))).1
  have eh := (abs_le.mp (euler656_error_high hRH (le_refl 1000000) hb)).1
  rw [mainDiff ha1 hav] at lo
  rw [mainDiff (by norm_num only) hb] at hi
  rw [lowDiff ha1 hav] at el
  rw [highDiff (by norm_num only) hb] at eh
  have hbm (k : ℕ) :=
    moment_nonneg (by norm_num only : (0 : ℝ) < 3 / 5) (show 1 ≤ b by linarith only [hb]) k
  have hbe (k : ℕ) :=
    moment_nonneg (by norm_num only : (0 : ℝ) < 11 / 10) (show 1 ≤ b by linarith only [hb]) k
  have hve (k : ℕ) :=
    moment_nonneg (by norm_num only : (0 : ℝ) < 11 / 10) (by norm_num only : (1 : ℝ) ≤ 1000000) k
  have hmb : 0 ≤ eulerMainTail656 b := by
    unfold eulerMainTail656
    linarith only [hbm 0, hbm 1, hbm 2]
  have heb : 0 ≤ eulerHighError656 b := by
    unfold eulerHighError656
    linarith only [hbe 2, hbe 3, hbe 4]
  have hev : 0 ≤ eulerLowError656 1000000 := by
    unfold eulerLowError656
    linarith only [hve 0, hve 1, hve 2]
  unfold signedTail656
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.floor_mono hav) (Nat.floor_mono hb),
    Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
  dsimp only [w]
  linear_combination lo + hi + el + eh + hmb + heb + hev

/-- The RH log-square bound and power decay force the upper Euler boundary to vanish. -/
private theorem upper_boundary_zero (hRH : RiemannHypothesis) :
    Filter.Tendsto (fun t ↦ (Chebyshev.psi t - t) * eulerDensity656 t) Filter.atTop (nhds 0) := by
  apply
    squeeze_zero_norm' _
      (Analysis.log_pow_mul_neg_rpow_tendsto (by norm_num only : (0 : ℝ) < 11 / 10) 4)
  filter_upwards [Filter.eventually_ge_atTop (1000000 : ℝ)] with t ht
  have hp : 0 < t := by linarith only [ht]
  have hl : 1 ≤ Real.log t :=
    (Real.le_log_iff_exp_le hp).mpr (Real.exp_one_lt_d9.le.trans (by linarith only [ht]))
  have hlog := zero_le_one.trans hl
  have hd : 0 ≤ eulerDensity656 t := by
    unfold eulerDensity656
    positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hd]
  apply (mul_le_mul_of_nonneg_right (euler570_psi_high hRH ht) hd).trans
  have hz : 3 / 8 + 33 / 80 * Real.log t + 121 / 800 * Real.log t ^ 2 ≤ 24 * Real.log t ^ 2 := by
    nlinarith only [hl, sq_nonneg (Real.log t - 1)]
  have he : Real.sqrt t * t ^ (-(8 / 5 : ℝ)) = t ^ (-(11 / 10 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
    norm_num only
  unfold eulerDensity656
  have hw : 0 ≤ Real.sqrt t * t ^ (-(8 / 5 : ℝ)) * (Real.log t ^ 2 / 24) := by positivity
  linear_combination mul_le_mul_of_nonneg_left hz hw + Real.log t ^ 4 * he

/-- Under RH the positive Euler tail above a real cutoff between 2701 and one million
is bounded by the explicit section 132 expression. Pass the finite upper bound to infinity
using summability and decay of the centered upper boundary. -/
theorem signed_tail_upper_656 (hRH : RiemannHypothesis) {a : ℝ} (ha : 2701 ≤ a)
    (hav : a ≤ 1000000) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * eulerDensity656 n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * eulerDensity656 n) ≤
      signedTail656 a := by
  have ht :=
    AnalyticNumberTheory.Arithmetic.tendsto_tail_prefix _
      (by simp only [ArithmeticFunction.map_zero, zero_mul]) euler_density_summable_656 a
  have hb :=
    (upper_boundary_zero hRH).comp
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
  have hr := hb.const_add (signedTail656 a)
  rw [add_zero] at hr
  apply le_of_tendsto_of_tendsto ht hr
  filter_upwards [Filter.eventually_ge_atTop (1000000 : ℕ)] with n hn
  have h := finite_tail_upper hRH ha hav (b := (n : ℝ)) (by exact_mod_cast hn)
  simpa only [Nat.floor_natCast, Function.comp_apply] using h

/-- Between cutoffs from 2701 through one million, the signed envelope
decreases by at least the Euler sum removed from the tail. The finite
Abel error is bounded by the difference of the low error moments. -/
theorem signed_tail_drop_656 {a b : ℝ} (ha : 2701 ≤ a) (hab : a ≤ b) (hb : b ≤ 1000000) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * eulerDensity656 n) ≤
      signedTail656 a - signedTail656 b := by
  have ha₁ : 1 ≤ a := by linarith only [ha]
  have h := euler656_abel (zero_lt_one.trans_le ha₁) hab
  have he := (abs_le.mp (euler656_error_million (by linarith only [ha]) hab hb)).1
  rw [mainDiff ha₁ hab] at h
  rw [lowDiff ha₁ hab] at he
  unfold signedTail656
  linarith only [h, he]

/-- The signed Euler tail envelope is antitone even at the jumps of psi
throughout the finite Abel range. Each removed Euler summand is nonnegative. -/
theorem signed_tail_antitone_656 : AntitoneOn signedTail656 (Set.Icc 2701 1000000) := by
  intro a ha b hb hab
  have h₀ :
    0 ≤ ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * eulerDensity656 n := by
    apply Finset.sum_nonneg
    intro n hn
    have hn₁ : (1 : ℝ) ≤ n :=
      Nat.one_le_cast.mpr (Nat.succ_le_of_lt (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1))
    have hlog := Real.log_nonneg hn₁
    unfold eulerDensity656
    positivity
  exact sub_nonneg.mp (h₀.trans (signed_tail_drop_656 ha.1 hab hb.2))

end PseudoPrime.PrimeTestBounds.MillerRabin
