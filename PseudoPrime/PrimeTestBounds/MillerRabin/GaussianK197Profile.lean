/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfileAbel663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxAbel656
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevBoundary43
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.EulerDerivatives
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbelInterval
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerError570

/-! # Combined Euler profile for the K197 auxiliary coefficients -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The six auxiliary coefficients of section 167.27, in the order of
the common frequencies `quarterFreq663`. -/
@[expose]
def gaussianCoeff197 (i : Fin 6) : ℚ :=
  (![497455957549, -521243909418, -48079634860, -43374900824, 132162470714, -117623471120] i) /
    1000000000000

/-- The shared Euler polynomial q plus the six-frequency quadratic and linear
terms with the K197 coefficients, including every ordered frequency pair. -/
@[expose]
noncomputable def gaussianProfile197 (v : ℝ) : ℝ :=
  quarterAuxProfile656 v +
      (∑ i : Fin 6,
          ∑ j : Fin 6,
            (gaussianCoeff197 i : ℝ) * (gaussianCoeff197 j : ℝ) *
              quarterAuxPair656 ((quarterFreq663 i - quarterFreq663 j : ℚ) : ℝ) v) /
        2 -
    ∑ i : Fin 6, (gaussianCoeff197 i : ℝ) * quarterAuxPair656 (quarterFreq663 i : ℝ) v

/-- The real coefficients of the actual centered combined profile. -/
private noncomputable def profileCoeff197 (k : Fin 3) : ℝ :=
  (shiftedCoeff k (23 / 2) : ℝ) +
      (∑ i : Fin 6,
          ∑ j : Fin 6,
            (gaussianCoeff197 i : ℝ) * (gaussianCoeff197 j : ℝ) *
              pairCoeff k (quarterFreq663 i - quarterFreq663 j)) /
        2 -
    ∑ i : Fin 6, (gaussianCoeff197 i : ℝ) * pairCoeff k (quarterFreq663 i)

/-- The matching exact rational coefficient approximations. -/
private def profileApprox197 (k : Fin 3) : ℚ :=
  shiftedCoeff k (23 / 2) +
      (∑ i : Fin 6,
          ∑ j : Fin 6,
            gaussianCoeff197 i * gaussianCoeff197 j *
              pairApprox k (quarterFreq663 i - quarterFreq663 j)) /
        2 -
    ∑ i : Fin 6, gaussianCoeff197 i * pairApprox k (quarterFreq663 i)

/-- The coefficient approximation keeps all six linear terms and all
36 ordered cross terms. -/
private theorem profile_coeff_error_197 (k : Fin 3) :
    |profileCoeff197 k - (profileApprox197 k : ℝ)| ≤ 1 / 10 ^ 12 := by
  have hpair :
    ∀ (i j : Fin 6) (k : Fin 3),
      let s := quarterFreq663 i - quarterFreq663 j
      abs ((11 / 10 : ℚ) * |s|) ≤ 11 ∧
        |shiftedCoeff k (23 / 2 + |s|)| ≤ 100 ∧ |shiftedCoeff k (23 / 2 - |s|)| ≤ 100 := by
    decide +kernel
  have hsingle :
    ∀ (i : Fin 6) (k : Fin 3),
      let s := quarterFreq663 i
      abs ((11 / 10 : ℚ) * |s|) ≤ 11 ∧
        |shiftedCoeff k (23 / 2 + |s|)| ≤ 100 ∧ |shiftedCoeff k (23 / 2 - |s|)| ≤ 100 := by
    unfold quarterFreq663
    decide +kernel
  have hc : ∀ i : Fin 6, |gaussianCoeff197 i| ≤ 1 := by decide +kernel
  have hc' (i : Fin 6) : |(gaussianCoeff197 i : ℝ)| ≤ 1 := by exact_mod_cast hc i
  have hweighted (i : Fin 6) {s : ℚ} (h : |pairCoeff k s - (pairApprox k s : ℝ)| ≤ 1 / 10 ^ 14) :
    |(gaussianCoeff197 i : ℝ) * pairCoeff k s - (gaussianCoeff197 i : ℝ) * (pairApprox k s : ℝ)| ≤
      1 / 10 ^ 14 := by
    rw [← mul_sub, abs_mul]
    exact (mul_le_mul (hc' i) h (abs_nonneg _) (by norm_num only)).trans_eq (one_mul _)
  have hlinear :=
    sum_six_error _ _ fun i ↦
      hweighted i (pair_coeff_error k _ (hsingle i k).1 (hsingle i k).2.1 (hsingle i k).2.2)
  have hinner (i : Fin 6) :=
    sum_six_error _ _ fun j ↦
      hweighted j (pair_coeff_error k _ (hpair i j k).1 (hpair i j k).2.1 (hpair i j k).2.2)
  have hquad :=
    sum_six_error
      (fun i ↦
        (gaussianCoeff197 i : ℝ) *
          ∑ j : Fin 6, (gaussianCoeff197 j : ℝ) * pairCoeff k (quarterFreq663 i - quarterFreq663 j))
      (fun i ↦
        (gaussianCoeff197 i : ℝ) *
          ∑ j : Fin 6,
            (gaussianCoeff197 j : ℝ) * (pairApprox k (quarterFreq663 i - quarterFreq663 j) : ℝ))
      fun i ↦ by
      rw [← mul_sub, abs_mul]
      exact (mul_le_mul (hc' i) (hinner i) (abs_nonneg _) (by norm_num only)).trans_eq (one_mul _)
  unfold profileCoeff197 profileApprox197
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_sum, Rat.cast_ofNat,
    mul_assoc, ← Finset.mul_sum]
  rw [show ∀ a b c d e : ℝ, a + b / 2 - c - (a + d / 2 - e) = (b - d) / 2 - (c - e) from
      fun a b c d e ↦ by ring]
  exact
    (abs_sub _ _).trans
      (by
        rw [abs_div, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
        linarith only [hlinear, hquad])

/-- Evaluate the centered real quadratic coefficients using exact
rational Taylor sums with the certified error. -/
private theorem profile_coeff_bounds_197 :
    profileCoeff197 0 ∈ Set.Icc 4.028662 4.028663 ∧
      profileCoeff197 1 ∈ Set.Icc (-7.025620) (-7.025619) ∧
      profileCoeff197 2 ∈ Set.Icc 2.061370 2.061371 := by
  have h :
    profileApprox197 0 ∈ Set.Icc (4.028662 + 1 / 10 ^ 12) (4.028663 - 1 / 10 ^ 12) ∧
      profileApprox197 1 ∈ Set.Icc (-7.025620 + 1 / 10 ^ 12) (-7.025619 - 1 / 10 ^ 12) ∧
      profileApprox197 2 ∈ Set.Icc (2.061370 + 1 / 10 ^ 12) (2.061371 - 1 / 10 ^ 12) := by
    decide +kernel
  have hb := fun k ↦ abs_le.mp (profile_coeff_error_197 k)
  have cast_box {x l u : ℚ} (hx : x ∈ Set.Icc l u) : (x : ℝ) ∈ Set.Icc (l : ℝ) (u : ℝ) :=
    ⟨(Rat.cast_le (K := ℝ)).mpr hx.1, (Rat.cast_le (K := ℝ)).mpr hx.2⟩
  have h₀ := cast_box h.1
  have h₁ := cast_box h.2.1
  have h₂ := cast_box h.2.2
  norm_num only [Set.mem_Icc, Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_one, Rat.cast_neg, Rat.cast_ofScientific] at h₀ h₁ h₂
  exact
    ⟨⟨by linarith only [h₀.1, (hb 0).1], by linarith only [h₀.2, (hb 0).2]⟩,
      ⟨by linarith only [h₁.1, (hb 1).1], by linarith only [h₁.2, (hb 1).2]⟩,
      ⟨by linarith only [h₂.1, (hb 2).1], by linarith only [h₂.2, (hb 2).2]⟩⟩

/-- The combined profile has the three certified coefficients in the
basis centered at 23/2. -/
private theorem profile_expand_197 (v : ℝ) :
    gaussianProfile197 v =
      profileCoeff197 0 + profileCoeff197 1 * (v - 23 / 2) +
        profileCoeff197 2 * (v - 23 / 2) ^ 2 := by
  unfold gaussianProfile197 profileCoeff197
  simp_rw [pair_profile_expand, mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul]
  simp only [quarterAuxProfile656, shiftedCoeff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_add, Rat.cast_mul, Rat.cast_pow]
  ring

/-- The signed physical reflected density for the K197 profile. -/
@[expose]
noncomputable def gaussianDensity197 (t : ℝ) : ℝ :=
  t ^ (-(8 / 5) : ℝ) * gaussianProfile197 (Real.log t)

/-- The derivative polynomial σ F - F' in displacement from 23/2. -/
noncomputable def gaussianSlope197 (x : ℝ) : ℝ :=
  ((8 / 5) * profileCoeff197 0 - profileCoeff197 1) +
    ((8 / 5) * profileCoeff197 1 - 2 * profileCoeff197 2) * x +
    (8 / 5) * profileCoeff197 2 * x ^ 2

/-- Differentiate the physical density with its actual signed profile. -/
theorem gaussian_density_deriv_197 {t : ℝ} (ht : 0 < t) :
    HasDerivAt gaussianDensity197 (-(t ^ (-(13 / 5) : ℝ)) * gaussianSlope197 (Real.log t - 23 / 2))
      t := by
  have hlog := (Real.hasDerivAt_log ht.ne').sub_const (23 / 2)
  have h :=
    (Real.hasDerivAt_rpow_const (p := -(8 / 5 : ℝ)) (Or.inl ht.ne')).mul
      (((hasDerivAt_const t (profileCoeff197 0)).add (hlog.const_mul (profileCoeff197 1))).add
        ((hlog.pow 2).const_mul (profileCoeff197 2)))
  have hp : t ^ (-(13 / 5) : ℝ) = t ^ (-(8 / 5) : ℝ) / t := by
    rw [show -(13 / 5 : ℝ) = -(8 / 5) - 1 by norm_num only, Real.rpow_sub ht, Real.rpow_one]
  convert h using 1
  · funext v
    simp only [gaussianDensity197, profile_expand_197, Pi.add_apply, Pi.pow_apply, Pi.mul_apply]
  · rw [show -(8 / 5 : ℝ) - 1 = -(13 / 5) by norm_num only, hp]
    simp only [gaussianSlope197, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat]
    ring

/-- On the nonnegative displacement half-line, bound the absolute
derivative polynomial by the coefficient enclosures. -/
theorem gaussian_slope_abs_197 {v : ℝ} (hv : 0 ≤ v) :
    |gaussianSlope197 v| ≤ 13.472 + 15.364 * v + 3.299 * v ^ 2 := by
  have h := profile_coeff_bounds_197
  have h₀ : |(8 / 5) * profileCoeff197 0 - profileCoeff197 1| ≤ (13.472 : ℝ) :=
    abs_le.mpr ⟨by linarith only [h.1.1, h.2.1.2], by linarith only [h.1.2, h.2.1.1]⟩
  have h₁ : |(8 / 5) * profileCoeff197 1 - 2 * profileCoeff197 2| ≤ (15.364 : ℝ) :=
    abs_le.mpr ⟨by linarith only [h.2.1.1, h.2.2.2], by linarith only [h.2.1.2, h.2.2.1]⟩
  have h₂ : |(8 / 5) * profileCoeff197 2| ≤ (3.299 : ℝ) :=
    abs_le.mpr ⟨by linarith only [h.2.2.1], by linarith only [h.2.2.2]⟩
  unfold gaussianSlope197
  apply (abs_add_le _ _).trans
  rw [abs_mul ((8 / 5 : ℝ) * profileCoeff197 2), abs_of_nonneg (sq_nonneg v)]
  apply add_le_add _ (mul_le_mul_of_nonneg_right h₂ (sq_nonneg v))
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg hv]
  exact add_le_add h₀ (mul_le_mul_of_nonneg_right h₁ hv)

/-- The main integrand is integrable on every tail above one. -/
private theorem density_integrable {x : ℝ} (hx : 1 ≤ x) :
    MeasureTheory.IntegrableOn gaussianDensity197 (Set.Ioi x) := by
  apply
    (aux_integrable_quad (d := 3 / 5) (by norm_num only) hx 0 (profileCoeff197 2)
        (profileCoeff197 1) (profileCoeff197 0) (23 / 2)).congr
  exact
    Filter.Eventually.of_forall fun t ↦ by
      simp only [gaussianDensity197, profile_expand_197, pow_zero, mul_one,
        show -(3 / 5 : ℝ) - 1 = -(8 / 5) by norm_num only]
      ring

/-- The improper main integral retains the exact signed coefficients. -/
private theorem profile_main {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in Set.Ioi x, gaussianDensity197 t) =
      x ^ (-(3 / 5) : ℝ) *
        (profileCoeff197 2 * Analysis.logPowerTailPoly (3 / 5) 2 (Real.log x) +
          (profileCoeff197 1 - 23 * profileCoeff197 2) *
            Analysis.logPowerTailPoly (3 / 5) 1 (Real.log x) +
          (profileCoeff197 0 - (23 / 2) * profileCoeff197 1 + (23 / 2) ^ 2 * profileCoeff197 2) *
            Analysis.logPowerTailPoly (3 / 5) 0 (Real.log x)) := by
  have h :=
    aux_integral_quad (d := 3 / 5) (by norm_num only) hx 0 (profileCoeff197 2) (profileCoeff197 1)
      (profileCoeff197 0) (23 / 2)
  have he (t : ℝ) :
    t ^ (-(3 / 5 : ℝ) - 1) * Real.log t ^ 0 *
        (profileCoeff197 2 * (Real.log t - 23 / 2) ^ 2 + profileCoeff197 1 * (Real.log t - 23 / 2) +
          profileCoeff197 0) =
      gaussianDensity197 t := by
    simp only [gaussianDensity197, profile_expand_197, pow_zero, mul_one,
      show -(3 / 5 : ℝ) - 1 = -(8 / 5) by norm_num only]
    ring
  simp only [he, Nat.zero_add] at h
  convert h using 1
  ring

/-- The Mangoldt-weighted signed series is absolutely convergent. -/
theorem gaussian_profile_summable_197 :
    Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * gaussianDensity197 n) := by
  have hm :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 8 / 5)
      (by norm_num only)
  let A := profileCoeff197 2
  let B := profileCoeff197 1
  let C := profileCoeff197 0
  let T : ℝ := 23 / 2
  apply
    (((hm 2).mul_left A).add ((hm 1).mul_left (B - 2 * A * T))).add
        ((hm 0).mul_left (C - B * T + A * T ^ 2)) |>.congr
  intro n
  simp only [gaussianDensity197, profile_expand_197, Real.rpow_neg (Nat.cast_nonneg n), pow_zero,
    pow_one, A, B, C, T, div_eq_mul_inv]
  ring

/-- The centered boundary vanishes by power decay of the three moments. -/
private theorem density_boundary :
    Filter.Tendsto (fun t : ℝ ↦ (Chebyshev.psi t - t) * gaussianDensity197 t) Filter.atTop
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
  let A := profileCoeff197 2
  let B := profileCoeff197 1
  let C := profileCoeff197 0
  let T : ℝ := 23 / 2
  have h :=
    (((hm 2).const_mul (4 * A)).add ((hm 1).const_mul (4 * (B - 2 * A * T)))).add
      ((hm 0).const_mul (4 * (C - B * T + A * T ^ 2)))
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  exact
    Filter.Eventually.of_forall
      (fun t ↦ by
        simp only [E, A, B, C, T, gaussianDensity197, profile_expand_197,
          AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight, pow_zero, pow_one]
        ring)

/-- At a cutoff above one, the signed Mangoldt tail equals its main
integral minus the two centered corrections. -/
theorem gaussian_profile_abel_197 {x : ℝ} (hx : 1 ≤ x)
    (he :
      MeasureTheory.IntegrableOn (fun t ↦ (Chebyshev.psi t - t) * deriv gaussianDensity197 t)
        (Set.Ioi x)) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * gaussianDensity197 n) -
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * gaussianDensity197 n =
      (∫ t in Set.Ioi x, gaussianDensity197 t) - (Chebyshev.psi x - x) * gaussianDensity197 x -
        ∫ t in Set.Ioi x, (Chebyshev.psi t - t) * deriv gaussianDensity197 t := by
  have hd (t : ℝ) (ht : 1 ≤ t) := gaussian_density_deriv_197 (zero_lt_one.trans_le ht)
  apply
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_integral (zero_le_one.trans hx)
      (fun _ _ t ht ↦ (hd t (hx.trans ht.1)).differentiableAt) _ (density_integrable hx) he
      density_boundary gaussian_profile_summable_197
  intro y _
  refine
    ContinuousOn.integrableOn_Icc (ContinuousOn.congr ?_ fun t ht ↦ (hd t (hx.trans ht.1)).deriv)
  intro t ht
  have ht₀ := (zero_lt_one.trans_le (hx.trans ht.1)).ne'
  have hl := Real.continuousAt_log ht₀
  have hpow := Real.continuousAt_rpow_const t (-(13 / 5 : ℝ)) (Or.inl ht₀)
  have hs : ContinuousAt (fun v ↦ gaussianSlope197 (Real.log v - 23 / 2)) t := by
    unfold gaussianSlope197
    fun_prop
  exact (hpow.neg.mul hs).continuousWithinAt

/-- The low Chebyshev majorant for the centered error. -/
private noncomputable def finiteMajor (t : ℝ) : ℝ :=
  (4 / 5) *
    (t ^ (-(21 / 10) : ℝ) *
      (13.472 + 15.364 * (Real.log t - 23 / 2) + 3.299 * (Real.log t - 23 / 2) ^ 2))

/-- The log-square RH majorant for the centered error. -/
private noncomputable def highMajor (t : ℝ) : ℝ :=
  (1 / 24) *
    (t ^ (-(21 / 10) : ℝ) * Real.log t ^ 2 *
      (13.472 + 15.364 * (Real.log t - 23 / 2) + 3.299 * (Real.log t - 23 / 2) ^ 2))

/-- The two moments majorize the centered error on their respective
ranges. The low majorant may also be retained on the high range. -/
private theorem profile_error_major (hRH : RiemannHypothesis) {t : ℝ} (ht : 1423 ≤ t)
    (hl : 23 / 2 ≤ Real.log t) :
    ‖(Chebyshev.psi t - t) * deriv gaussianDensity197 t‖ ≤
      finiteMajor t + (Set.Ioi (1000000 : ℝ)).indicator highMajor t := by
  have ht₀ : 0 < t := by linarith only [ht]
  have hlog := sub_nonneg.mpr hl
  have he : Real.sqrt t * t ^ (-(13 / 5) : ℝ) = t ^ (-(21 / 10) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht₀]
    norm_num only
  have hd := (gaussian_density_deriv_197 ht₀).deriv
  rw [hd, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_nonneg (Real.rpow_nonneg ht₀.le _)]
  have hS :=
    mul_le_mul_of_nonneg_left (gaussian_slope_abs_197 hlog) (Real.rpow_nonneg ht₀.le (-(13 / 5)))
  have hS₀ :=
    mul_nonneg (Real.rpow_nonneg ht₀.le (-(13 / 5)))
      (abs_nonneg (gaussianSlope197 (Real.log t - 23 / 2)))
  by_cases h : t ≤ 1000000
  · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (1000000 : ℝ) from not_lt.mpr h), add_zero]
    have hψ := AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million ht h
    unfold finiteMajor
    linear_combination
      (mul_le_mul hψ hS hS₀ (by positivity)) +
        (4 / 5) * (13.472 + 15.364 * (Real.log t - 23 / 2) + 3.299 * (Real.log t - 23 / 2) ^ 2) * he
  · have h' : t ∈ Set.Ioi (1000000 : ℝ) := lt_of_not_ge h
    rw [Set.indicator_of_mem h']
    have hψ := euler570_psi_high hRH h'.le
    have hF : 0 ≤ finiteMajor t := by
      unfold finiteMajor; positivity
    unfold highMajor
    linear_combination
      (mul_le_mul hψ hS hS₀ (by positivity)) + hF +
        (Real.log t ^ 2 / 24) *
          (13.472 + 15.364 * (Real.log t - 23 / 2) + 3.299 * (Real.log t - 23 / 2) ^ 2) *
          he

/-- The finite-error majorant is integrable by three logarithmic moments. -/
private theorem finite_major_integrable {x : ℝ} (hx₁ : 1 ≤ x) :
    MeasureTheory.IntegrableOn finiteMajor (Set.Ioi x) := by
  apply
    ((aux_integrable_quad (d := 11 / 10) (by norm_num only) hx₁ 0 3.299 15.364 13.472
            (23 / 2)).const_mul
        (4 / 5 : ℝ)).congr
  exact
    Filter.Eventually.of_forall fun t ↦ by
      simp only [finiteMajor, pow_zero, mul_one,
        show -(11 / 10 : ℝ) - 1 = -(21 / 10) by norm_num only]
      ring

/-- The high-error majorant is integrable by moments of degrees two through four. -/
private theorem high_major_integrable : MeasureTheory.IntegrableOn highMajor (Set.Ioi 1000000) := by
  have h :=
    aux_integrable_quad (d := 11 / 10) (by norm_num only) (by norm_num only : (1 : ℝ) ≤ 1000000) 2
      3.299 15.364 13.472 (23 / 2)
  apply (h.const_mul (1 / 24 : ℝ)).congr
  exact
    Filter.Eventually.of_forall fun t ↦ by
      simp only [highMajor, show -(11 / 10 : ℝ) - 1 = -(21 / 10) by norm_num only]
      ring

/-- The centered remainder is integrable at every K197 cutoff. -/
private theorem profile_error_integrable (hRH : RiemannHypothesis) {x : ℝ} (hx : 1423 ≤ x)
    (hl : 23 / 2 ≤ Real.log x) :
    MeasureTheory.IntegrableOn (fun t ↦ (Chebyshev.psi t - t) * deriv gaussianDensity197 t)
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
          (measurable_deriv gaussianDensity197)).aestronglyMeasurable)
      ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  exact
    profile_error_major hRH (hx.trans ht.le)
      (hl.trans (Real.log_le_log (zero_lt_one.trans_le hx₁) ht.le))

/-- Under RH, the improper signed Abel identity applies at a K197
cutoff with no extra integrability hypothesis. -/
theorem gaussian_profile_signed_abel_197 (hRH : RiemannHypothesis) {x : ℝ} (hx : 1423 ≤ x)
    (hl : 23 / 2 ≤ Real.log x) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * gaussianDensity197 n) -
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * gaussianDensity197 n =
      (∫ t in Set.Ioi x, gaussianDensity197 t) - (Chebyshev.psi x - x) * gaussianDensity197 x -
        ∫ t in Set.Ioi x, (Chebyshev.psi t - t) * deriv gaussianDensity197 t :=
  gaussian_profile_abel_197 (by linarith only [hx]) (profile_error_integrable hRH hx hl)

/-- The sum of the two improper error majorants for the K197 profile,
with the exact lower cutoff retained in the finite-envelope term. -/
noncomputable def gaussianAbelError197 (x : ℝ) : ℝ :=
  (∫ t in Set.Ioi x, finiteMajor t) + ∫ t in Set.Ioi (max x (1000000 : ℝ)), highMajor t

/-- At a K197 cutoff, the two explicit moments
bound the signed tail error while preserving the exact lower boundary. -/
theorem gaussian_profile_tail_upper_197 (hRH : RiemannHypothesis) {x : ℝ} (hx : 1423 ≤ x)
    (hl : 23 / 2 ≤ Real.log x) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * gaussianDensity197 n) -
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * gaussianDensity197 n ≤
      (∫ t in Set.Ioi x, gaussianDensity197 t) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x := by
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
    ‖∫ t in Set.Ioi x, (Chebyshev.psi t - t) * deriv gaussianDensity197 t‖ ≤
      ∫ t in Set.Ioi x, finiteMajor t + (Set.Ioi (1000000 : ℝ)).indicator highMajor t at he
  rw [Real.norm_eq_abs, MeasureTheory.integral_add hm hi,
    MeasureTheory.setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi] at he
  unfold gaussianAbelError197
  linarith only [gaussian_profile_signed_abel_197 hRH hx hl, (abs_le.mp he).1]

/-- Bound the signed main integral via the centered quadratic coefficients.
The cutoff assumptions make the multipliers of all three coefficients nonnegative. -/
theorem gaussian_profile_main_upper_197 {x : ℝ} (hx : 1 ≤ x) (hl : 23 / 2 ≤ Real.log x) :
    let v := Real.log x - 23 / 2
    (∫ t in Set.Ioi x, gaussianDensity197 t) ≤
      x ^ (-(3 / 5) : ℝ) *
        ((4.028663 - 7.025619 * (v + 5 / 3) + 2.061371 * (v ^ 2 + (10 / 3) * v + 50 / 9)) /
          (3 / 5)) := by
  intro v
  have he :
    (∫ t in Set.Ioi x, gaussianDensity197 t) =
      x ^ (-(3 / 5) : ℝ) *
        ((profileCoeff197 0 + profileCoeff197 1 * (v + 5 / 3) +
            profileCoeff197 2 * (v ^ 2 + (10 / 3) * v + 50 / 9)) /
          (3 / 5)) := by
    rw [profile_main hx]
    norm_num only [v, Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
      Nat.reduceAdd]
    ring
  have hv : 0 ≤ v := sub_nonneg.mpr hl
  have h := profile_coeff_bounds_197
  have h₁ := mul_le_mul_of_nonneg_right h.2.1.2 (by linarith only [hv] : 0 ≤ v + 5 / 3)
  have h₂ := mul_le_mul_of_nonneg_right h.2.2.2 (by positivity : 0 ≤ v ^ 2 + (10 / 3) * v + 50 / 9)
  rw [he]
  exact
    mul_le_mul_of_nonneg_left (by linarith only [h.1.2, h₁, h₂])
      (Real.rpow_nonneg (zero_le_one.trans hx) _)

private theorem major_integral_formula {x : ℝ} (hx : 1 ≤ x) (k : ℕ) :
    (∫ t in Set.Ioi x,
        t ^ (-(21 / 10) : ℝ) * Real.log t ^ k *
          (13.472 + 15.364 * (Real.log t - 23 / 2) + 3.299 * (Real.log t - 23 / 2) ^ 2)) =
      x ^ (-(11 / 10) : ℝ) *
        (3.299 * Analysis.logPowerTailPoly (11 / 10) (k + 2) (Real.log x) -
            60.513 * Analysis.logPowerTailPoly (11 / 10) (k + 1) (Real.log x) +
          273.07875 * Analysis.logPowerTailPoly (11 / 10) k (Real.log x)) := by
  have h := aux_integral_quad (d := 11 / 10) (by norm_num only) hx k 3.299 15.364 13.472 (23 / 2)
  simp only [show -(11 / 10 : ℝ) - 1 = -(21 / 10) by norm_num only] at h
  convert h using 1
  · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  · ring

private theorem finite_major_integral {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in Set.Ioi x, finiteMajor t) =
      (4 / 5) *
        (x ^ (-(11 / 10) : ℝ) *
          (3.299 * Analysis.logPowerTailPoly (11 / 10) 2 (Real.log x) -
              60.513 * Analysis.logPowerTailPoly (11 / 10) 1 (Real.log x) +
            273.07875 * Analysis.logPowerTailPoly (11 / 10) 0 (Real.log x))) := by
  simp only [finiteMajor]
  rw [MeasureTheory.integral_const_mul]
  rw [← major_integral_formula hx 0]
  simp only [pow_zero, mul_one]

private theorem high_major_integral :
    (∫ t in Set.Ioi (1000000 : ℝ), highMajor t) =
      (1 / 24) *
        ((1000000 : ℝ) ^ (-(11 / 10) : ℝ) *
          (3.299 * Analysis.logPowerTailPoly (11 / 10) 4 (Real.log 1000000) -
              60.513 * Analysis.logPowerTailPoly (11 / 10) 3 (Real.log 1000000) +
            273.07875 * Analysis.logPowerTailPoly (11 / 10) 2 (Real.log 1000000))) := by
  simp only [highMajor]
  rw [MeasureTheory.integral_const_mul]
  rw [← major_integral_formula (by norm_num only : (1 : ℝ) ≤ 1000000) 2]

/-- Evaluate both K197 majorants at their exact cutoffs below one million.
Only logarithms and rational powers remain in the resulting error bound. -/
theorem gaussian_abel_error_formula_197 {x : ℝ} (hx : 1 ≤ x) (hU : x ≤ 1000000) :
    gaussianAbelError197 x =
      (4 / 5) *
          (x ^ (-(11 / 10) : ℝ) *
            (3.299 * Analysis.logPowerTailPoly (11 / 10) 2 (Real.log x) -
                60.513 * Analysis.logPowerTailPoly (11 / 10) 1 (Real.log x) +
              273.07875 * Analysis.logPowerTailPoly (11 / 10) 0 (Real.log x))) +
        (1 / 24) *
          ((1000000 : ℝ) ^ (-(11 / 10) : ℝ) *
            (3.299 * Analysis.logPowerTailPoly (11 / 10) 4 (Real.log 1000000) -
                60.513 * Analysis.logPowerTailPoly (11 / 10) 3 (Real.log 1000000) +
              273.07875 * Analysis.logPowerTailPoly (11 / 10) 2 (Real.log 1000000))) := by
  rw [gaussianAbelError197, max_eq_right hU, finite_major_integral hx, high_major_integral]

private theorem abel_major_poly_bound {z l u : ℝ} (hl : 0 ≤ l) (hz : z ∈ Set.Icc l u) (k : ℕ) :
    3.299 * Analysis.logPowerTailPoly (11 / 10) (k + 2) z -
          60.513 * Analysis.logPowerTailPoly (11 / 10) (k + 1) z +
        273.07875 * Analysis.logPowerTailPoly (11 / 10) k z ≤
      3.299 * Analysis.logPowerTailPoly (11 / 10) (k + 2) u -
          60.513 * Analysis.logPowerTailPoly (11 / 10) (k + 1) l +
        273.07875 * Analysis.logPowerTailPoly (11 / 10) k u := by
  have hm {v w : ℝ} (hv : 0 ≤ v) (hw : v ≤ w) (j : ℕ) :=
    Analysis.log_power_tail_poly_mono (by norm_num only : (0 : ℝ) < 11 / 10) hv hw j
  linarith only [hm (hl.trans hz.1) hz.2 (k + 2), hm hl hz.1 (k + 1), hm (hl.trans hz.1) hz.2 k]

private theorem finite_major_early_bound :
    (∫ t in Set.Ioi (110000 : ℝ), finiteMajor t) ≤ 0.000074 := by
  rw [finite_major_integral (by norm_num only)]
  have hlog :=
    Analysis.rationalLogIntervalCheck_sound (N := 110000) (j := 17) (n := 32) (lo := 11.60823)
      (hi := 11.60824) (by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlog
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 110000) (p := 11) (d :=
        10) (lo := 0) (hi := 0.000002848) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  have h := abel_major_poly_bound (by norm_num only) hlog 0
  have hB := h.trans (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat] : _ ≤ (32.1 : ℝ))
  have hm :=
    (mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right hp (by norm_num only))
  linarith only [hm]

private theorem high_major_early_bound :
    (∫ t in Set.Ioi (1000000 : ℝ), highMajor t) ≤ 0.000218 := by
  rw [high_major_integral]
  have hlog :=
    Analysis.rationalLogIntervalCheck_sound (N := 1000000) (j := 20) (n := 32) (lo := 13.8155105)
      (hi := 13.8155106) (by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlog
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1000000) (p := 11) (d :=
        10) (lo := 0) (hi := 0.000000251189) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  have h := abel_major_poly_bound (by norm_num only) hlog 2
  have hB :=
    h.trans (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat] : _ ≤ (20805 : ℝ))
  have hm :=
    (mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right hp (by norm_num only))
  linarith only [hm]

/-- The K197 Abel error is at most 0.000292 for any cutoff from 110000 onward.
Both nonnegative majorants decrease when the integration domain shrinks. -/
theorem gaussian_abel_error_uniform_197 {x : ℝ} (hx : 110000 ≤ x) :
    gaussianAbelError197 x ≤ 0.000292 := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 110000) (j := 17) (n := 32) (lo := 11.5) (hi :=
        12) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlog
  have hnon : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioi (110000 : ℝ)), 0 ≤ finiteMajor t := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hl := hlog.trans (Real.log_le_log (by norm_num only) ht.le)
    have h₀ : 0 ≤ Real.log t - 23 / 2 := by linarith only [hl]
    unfold finiteMajor
    exact
      mul_nonneg (by norm_num only)
        (mul_nonneg (Real.rpow_nonneg ((by norm_num only : (0 : ℝ) ≤ 110000).trans ht.le) _)
          (add_nonneg (add_nonneg (by norm_num only) (mul_nonneg (by norm_num only) h₀))
            (mul_nonneg (by norm_num only) (sq_nonneg _))))
  have h :=
    MeasureTheory.setIntegral_mono_set
      (finite_major_integrable (by norm_num only : (1 : ℝ) ≤ 110000)) hnon
      (Filter.Eventually.of_forall (Set.Ioi_subset_Ioi hx))
  have hhigh : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioi (1000000 : ℝ)), 0 ≤ highMajor t := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₀ := (by norm_num only : (0 : ℝ) ≤ 1000000).trans ht.le
    have hl :=
      hlog.trans
        (Real.log_le_log (by norm_num only)
          ((by norm_num only : (110000 : ℝ) ≤ 1000000).trans ht.le))
    have hz : 0 ≤ Real.log t - 23 / 2 := by linarith only [hl]
    unfold highMajor
    exact
      mul_nonneg (by norm_num only)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg ht₀ _) (sq_nonneg _))
          (add_nonneg (add_nonneg (by norm_num only) (mul_nonneg (by norm_num only) hz))
            (mul_nonneg (by norm_num only) (sq_nonneg _))))
  have hh :=
    MeasureTheory.setIntegral_mono_set high_major_integrable hhigh
      (Filter.Eventually.of_forall (Set.Ioi_subset_Ioi (le_max_right x (1000000 : ℝ))))
  change
    (∫ t in Set.Ioi x, finiteMajor t) + (∫ t in Set.Ioi (max x (1000000 : ℝ)), highMajor t) ≤
      0.000292
  linarith only [h, hh, finite_major_early_bound, high_major_early_bound]

/-- The same Abel error bound applies to the early K197 cutoffs through one million. -/
theorem gaussian_abel_error_early_197 {x : ℝ} (hx : 110000 ≤ x) (_hU : x ≤ 1000000) :
    gaussianAbelError197 x ≤ 0.000292 :=
  gaussian_abel_error_uniform_197 hx

end PseudoPrime.PrimeTestBounds.MillerRabin
