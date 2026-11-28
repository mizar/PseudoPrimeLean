/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighPrincipalCenter
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaRational
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPole

/-! # Finite exponential moments in the high Gaussian gamma bound -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The complete Laplace transform of the normalized physical profile,
represented directly by its partial-fraction coefficients. -/
@[expose]
public noncomputable def highProfileLaplace (K : HighGaussianKernel) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (2 * K.degree + 1), (K.expandedCoeff j : ℝ) / s ^ (K.logPower j + 1)

/-- Away from zero, the complete transform in H36 reassembles into the
normalized square of the compact numerator. -/
public theorem high_profile_laplace_square (K : HighGaussianKernel) {s : ℝ} (hs : s ≠ 0) :
    highProfileLaplace K s =
      (K.normalization : ℝ) * (K.polynomial.eval₂ (Rat.castHom ℝ) s) ^ 2 /
        s ^ (2 * K.degree + 4) := by
  have hd := (Polynomial.natDegree_pow_le_of_le 2 (high_gaussian_polynomial_degree K))
  have he := Polynomial.eval₂_eq_sum_range' (Rat.castHom ℝ) (Nat.lt_succ_of_le hd) s
  rw [Polynomial.eval₂_pow] at he
  rw [highProfileLaplace, he, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ 2 * K.degree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hk : K.logPower j + 1 + j = 2 * K.degree + 4 := by
    unfold HighGaussianKernel.logPower
    change (2 * K.degree - j + 4) + j = 2 * K.degree + 4
    rw [Nat.add_right_comm, Nat.sub_add_cancel hj']
  rw [← hk, pow_add s (K.logPower j + 1) j, HighGaussianKernel.expandedCoeff, Rat.cast_mul, ←
    mul_assoc, mul_div_mul_right _ _ (pow_ne_zero _ hs)]
  rfl

/-- At every positive decay rate the complete profile integral equals the
finite partial-fraction sum and is absolutely integrable. -/
public theorem high_profile_laplace_eq (K : HighGaussianKernel) {s : ℝ} (hs : 0 < s) :
    let f := fun t : ℝ ↦ K.realProfile.eval t * Real.exp (-s * t)
    MeasureTheory.IntegrableOn f (Set.Ioi 0) ∧
      (∫ t in Set.Ioi (0 : ℝ), f t) = highProfileLaplace K s := by
  intro f
  let c := fun j ↦ (K.expandedCoeff j : ℝ) / ((K.logPower j).factorial : ℝ)
  let g := fun j t ↦ c j * (t ^ K.logPower j * Real.exp (-s * t))
  have he : f = fun t ↦ ∑ j ∈ Finset.range (2 * K.degree + 1), g j t := by
    funext t
    simp only [f, g, c, HighGaussianKernel.realProfile, Polynomial.eval_finsetSum,
      Polynomial.eval_monomial, Finset.sum_mul, mul_assoc]
  have hg (j : ℕ) := (exp_monomial_integrable (K.logPower j) hs).const_mul (c j)
  rw [he]
  refine ⟨MeasureTheory.integrable_finsetSum _ (fun j _ ↦ hg j), ?_⟩
  rw [MeasureTheory.integral_finsetSum _ (fun j _ ↦ hg j)]
  apply Finset.sum_congr rfl
  intro j _
  change
    (∫ t in Set.Ioi (0 : ℝ), c j * (t ^ K.logPower j * Real.exp (-s * t))) =
      (K.expandedCoeff j : ℝ) / s ^ (K.logPower j + 1)
  rw [MeasureTheory.integral_const_mul, exp_monomial_integral _ hs]
  dsimp only [c]
  have hfac : ((K.logPower j).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  rw [div_mul_div_comm, mul_comm ((K.logPower j).factorial : ℝ), mul_div_mul_right _ _ hfac]

/-- The finite moment in H36 is the complete profile transform less the
exact signed tail. This identity retains the cancellation at the cutoff. -/
public theorem high_profile_finite_laplace (K : HighGaussianKernel) {s z : ℝ} (hs : 0 < s)
    (hz : 0 ≤ z) :
    let Q := K.realProfile.comp (Polynomial.X + Polynomial.C z)
    (∫ t in (0 : ℝ)..z, K.realProfile.eval t * Real.exp (-s * t)) =
      highProfileLaplace K s -
        Real.exp (-s * z) *
          ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((k.factorial : ℝ) / s ^ (k + 1)) := by
  intro Q
  have h := high_profile_laplace_eq K hs
  rw [← intervalIntegral.integral_Ioi_sub_Ioi h.1 hz, h.2, polynomial_exp_tail K.realProfile z hs]

/-- The convolution form of the finite gamma moment in H36 cancels the
exponential factor of the signed tail exactly. -/
public theorem high_gamma_conv_moment (K : HighGaussianKernel) {s z : ℝ} (hs : 0 < s) (hz : 0 ≤ z) :
    let Q := K.realProfile.comp (Polynomial.X + Polynomial.C z)
    (∫ t in (0 : ℝ)..z, Real.exp (s * (z - t)) * K.realProfile.eval t) =
      Real.exp (s * z) * highProfileLaplace K s -
        ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((k.factorial : ℝ) / s ^ (k + 1)) := by
  intro Q
  have he (t : ℝ) :
    Real.exp (s * (z - t)) * K.realProfile.eval t =
      Real.exp (s * z) * (K.realProfile.eval t * Real.exp (-s * t)) := by
    rw [mul_sub, sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc, mul_comm (Real.exp (-(s * t)))]
  simp only [he]
  rw [intervalIntegral.integral_const_mul, high_profile_finite_laplace K hs hz, mul_sub, ←
    mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, one_mul]

/-- A two-sided coefficient bound controls a signed product by the upper endpoint
plus a correction on the negative part, as in H34. -/
public theorem high_gamma_mul_le {g l u b : ℝ} (hl : l ≤ g) (hu : g ≤ u) :
    g * b ≤ u * b + (u - l) * max (-b) 0 := by
  by_cases hb : 0 ≤ b
  · rw [max_eq_right (neg_nonpos.mpr hb), mul_zero, add_zero]
    exact mul_le_mul_of_nonneg_right hu hb
  · rw [max_eq_left (neg_nonneg.mpr (le_of_not_ge hb))]
    have h := mul_le_mul_of_nonpos_right hl (le_of_not_ge hb)
    linarith only [h]

/-- A nonnegative increment of a continuous integrand cannot increase the
negative part of its accumulated integral. This applies to the H37 moment
with integrand `B(t) * exp(-d*t)`. -/
public theorem high_gamma_moment_neg_le {f : ℝ → ℝ} {a z : ℝ} (h : a ≤ z) (hf : Continuous f)
    (hs : ∀ t ∈ Set.Icc a z, 0 ≤ f t) :
    max (-(∫ t in (0 : ℝ)..z, f t)) 0 ≤ max (-(∫ t in (0 : ℝ)..a, f t)) 0 := by
  have hp := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) h hs
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 a) (hf.intervalIntegrable a z)
  exact max_le_max (by linarith only [hp, hadd]) le_rfl

/-- If the physical profile is nonnegative from the cutoff to the evaluation
point, the negative part of the H37 convolution grows at most by the
exponential factor over that interval. -/
public theorem high_gamma_conv_neg_le (K : HighGaussianKernel) {s a z : ℝ} (haz : a ≤ z)
    (hs : ∀ t ∈ Set.Icc a z, 0 ≤ K.realProfile.eval t) :
    max (-(∫ t in (0 : ℝ)..z, Real.exp (s * (z - t)) * K.realProfile.eval t)) 0 ≤
      Real.exp (s * (z - a)) *
        max (-(∫ t in (0 : ℝ)..a, Real.exp (s * (a - t)) * K.realProfile.eval t)) 0 := by
  let f := fun t ↦ Real.exp (s * (z - t)) * K.realProfile.eval t
  have hf : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).mul
      K.realProfile.continuous
  have hp :=
    intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) haz
      (fun t ht ↦ mul_nonneg (Real.exp_pos _).le (hs t ht) : ∀ t ∈ Set.Icc a z, 0 ≤ f t)
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 a) (hf.intervalIntegrable a z)
  have he (t : ℝ) :
    f t = Real.exp (s * (z - a)) * (Real.exp (s * (a - t)) * K.realProfile.eval t) := by
    rw [← mul_assoc, ← Real.exp_add]
    dsimp only [f]
    congr 2
    ring
  calc
    _ ≤ max (-(∫ t in (0 : ℝ)..a, f t)) 0 := max_le_max (by linarith only [hp, hadd]) le_rfl
    _ = _ := by
      simp only [he, intervalIntegral.integral_const_mul, mul_max_of_nonneg _ _ (Real.exp_pos _).le,
        mul_zero, mul_neg]

/-- The compact rational evaluation agrees with the complete real transform. -/
public theorem high_gamma_transform_cast (K : HighGaussianKernel) (s : ℚ) :
    (highGammaRatTransform K s : ℝ) = highProfileLaplace K (s : ℝ) := by
  by_cases hs : s = 0
  · simp only [hs, high_gamma_rat_transform_eq, highProfileLaplace, zero_pow (Nat.succ_ne_zero _),
      div_zero, Rat.cast_zero, Finset.sum_const_zero]
  · rw [high_profile_laplace_square K (Rat.cast_ne_zero.mpr hs), high_gamma_rat_transform_eq,
      Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_pow]
    have h := eval_cast_map (RingHom.id ℚ) (Rat.castHom ℝ) K.polynomial s
    simpa only [RingHom.comp_id, Rat.coe_castHom] using
      congrArg (fun v : ℝ ↦ (K.normalization : ℝ) * v ^ 2 / (s : ℝ) ^ (2 * K.degree + 4)) h

end PseudoPrime.PrimeTestBounds.MillerRabin
