/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Fourier mode integrals for the high Gaussian kernel after the cotangent substitution. -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An integer Fourier mode integrates to zero over a full period in the
double-angle variable, except for the constant mode. -/
public theorem high_gaussian_angle_mode (k : ℤ) :
    (∫ θ in (0 : ℝ)..Real.pi, Complex.exp (2 * (k : ℂ) * Complex.I * (θ : ℂ))) =
      if k = 0 then (Real.pi : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, ite_true,
      intervalIntegral.integral_const, sub_zero, Complex.real_smul, mul_one]
  · have hc : (2 : ℂ) * (k : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num only) (Int.cast_ne_zero.mpr hk)) Complex.I_ne_zero
    rw [ite_eq_right hk, integral_exp_mul_complex hc]
    have he :
      (2 * (k : ℂ) * Complex.I) * (Real.pi : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      ring
    rw [he, Complex.exp_int_mul_two_pi_mul_I, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      sub_self, zero_div]

/-- The double-angle exponential of integer frequency `k` at `θ`. -/
private noncomputable def angleMode (k : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp (2 * (k : ℂ) * Complex.I * (θ : ℂ))

/-- The sine-square weight couples a mode only with its two adjacent modes. -/
private theorem angle_mode_mul_sin_sq (k : ℤ) (θ : ℝ) :
    ((Real.sin θ ^ 2 : ℝ) : ℂ) * angleMode k θ =
      (1 / 2 : ℂ) * angleMode k θ -
        ((1 / 4 : ℂ) * angleMode (k + 1) θ + (1 / 4 : ℂ) * angleMode (k - 1) θ) := by
  have hp : angleMode (k + 1) θ = Complex.exp ((2 * (θ : ℂ)) * Complex.I) * angleMode k θ := by
    unfold angleMode
    rw [← Complex.exp_add, Int.cast_add, Int.cast_one]
    congr 1
    ring
  have hm : angleMode (k - 1) θ = Complex.exp (-(2 * (θ : ℂ)) * Complex.I) * angleMode k θ := by
    unfold angleMode
    rw [← Complex.exp_add, Int.cast_sub, Int.cast_one]
    congr 1
    ring
  rw [hp, hm, Real.sin_sq_eq_half_sub]
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_cos, Complex.ofReal_mul, Complex.cos]
  ring

/-- The sine-square weighted Fourier integral has only three nonzero diagonals. -/
public theorem high_gaussian_angle_weight (k : ℤ) :
    (∫ θ in (0 : ℝ)..Real.pi,
        ((Real.sin θ ^ 2 : ℝ) : ℂ) * Complex.exp (2 * (k : ℂ) * Complex.I * (θ : ℂ))) =
      (1 / 2 : ℂ) * (if k = 0 then (Real.pi : ℂ) else 0) -
        ((1 / 4 : ℂ) * (if k + 1 = 0 then (Real.pi : ℂ) else 0) +
          (1 / 4 : ℂ) * (if k - 1 = 0 then (Real.pi : ℂ) else 0)) := by
  have hc (j : ℤ) : Continuous (angleMode j) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hi (c : ℂ) (j : ℤ) :
    IntervalIntegrable (fun θ ↦ c * angleMode j θ) MeasureTheory.volume 0 Real.pi :=
    (continuous_const.mul (hc j)).intervalIntegrable _ _
  change (∫ θ in (0 : ℝ)..Real.pi, ((Real.sin θ ^ 2 : ℝ) : ℂ) * angleMode k θ) = _
  simp only [angle_mode_mul_sin_sq]
  rw [intervalIntegral.integral_sub (hi _ _) ((hi _ _).add (hi _ _)),
    intervalIntegral.integral_add (hi _ _) (hi _ _)]
  simp only [intervalIntegral.integral_const_mul, angleMode, high_gaussian_angle_mode]

/-- Integrate a finite sum of double-angle modes against the sine-square weight. -/
public theorem high_gaussian_angle_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (k : ι → ℤ) :
    (∫ θ in (0 : ℝ)..Real.pi,
        ((Real.sin θ ^ 2 : ℝ) : ℂ) *
          ∑ i ∈ s, c i * Complex.exp (2 * (k i : ℂ) * Complex.I * (θ : ℂ))) =
      ∑ i ∈ s,
        c i *
          ((1 / 2 : ℂ) * (if k i = 0 then (Real.pi : ℂ) else 0) -
            ((1 / 4 : ℂ) * (if k i + 1 = 0 then (Real.pi : ℂ) else 0) +
              (1 / 4 : ℂ) * (if k i - 1 = 0 then (Real.pi : ℂ) else 0))) := by
  have hc (i : ι) : Continuous (angleMode (k i)) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hs : Continuous (fun θ : ℝ ↦ ((Real.sin θ ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sin.pow 2)
  have hi (i : ι) :
    IntervalIntegrable (fun θ ↦ c i * (((Real.sin θ ^ 2 : ℝ) : ℂ) * angleMode (k i) θ))
      MeasureTheory.volume 0 Real.pi :=
    (continuous_const.mul (hs.mul (hc i))).intervalIntegrable _ _
  simp only [Finset.mul_sum, mul_left_comm (((Real.sin _ ^ 2 : ℝ) : ℂ)) (c _)]
  rw [intervalIntegral.integral_finsetSum (s := s)
      (fun i _ ↦
        (show
          IntervalIntegrable
            (fun θ ↦
              c i *
                (((Real.sin θ ^ 2 : ℝ) : ℂ) * Complex.exp (2 * (k i : ℂ) * Complex.I * (θ : ℂ))))
            MeasureTheory.volume 0 Real.pi
          from hi i))]
  simp only [intervalIntegral.integral_const_mul, high_gaussian_angle_weight]

/-- Multiplication by a conjugate mode subtracts its frequency. -/
private theorem angle_mode_mul_conj (j k : ℤ) (θ : ℝ) :
    angleMode j θ * (starRingEnd ℂ) (angleMode k θ) = angleMode (j - k) θ := by
  unfold angleMode
  rw [← Complex.exp_conj, ← Complex.exp_add, Int.cast_sub]
  simp only [map_mul, map_intCast, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  ring

/-- The product of a finite Fourier sum and its conjugate is indexed by frequency differences. -/
public theorem high_gaussian_angle_norm_sq {ι : Type*} (s : Finset ι) (c : ι → ℂ) (k : ι → ℤ)
    (θ : ℝ) :
    ((‖∑ i ∈ s, c i * Complex.exp (2 * (k i : ℂ) * Complex.I * (θ : ℂ))‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ s ×ˢ s,
        (c p.1 * (starRingEnd ℂ) (c p.2)) *
          Complex.exp (2 * ((k p.1 - k p.2 : ℤ) : ℂ) * Complex.I * (θ : ℂ)) := by
  change
    ((‖∑ i ∈ s, c i * angleMode (k i) θ‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ s ×ˢ s, (c p.1 * (starRingEnd ℂ) (c p.2)) * angleMode (k p.1 - k p.2) θ
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, ← angle_mode_mul_conj]
  ac_rfl

/-- The weighted squared norm of a finite Fourier sum is its three-diagonal Gram sum. -/
public theorem high_gaussian_angle_gram {ι : Type*} (s : Finset ι) (c : ι → ℂ) (k : ι → ℤ) :
    (∫ θ in (0 : ℝ)..Real.pi,
        ((Real.sin θ ^ 2 : ℝ) : ℂ) *
          ((‖∑ i ∈ s, c i * Complex.exp (2 * (k i : ℂ) * Complex.I * (θ : ℂ))‖ ^ 2 : ℝ) : ℂ)) =
      ∑ p ∈ s ×ˢ s,
        (c p.1 * (starRingEnd ℂ) (c p.2)) *
          ((1 / 2 : ℂ) * (if k p.1 - k p.2 = 0 then (Real.pi : ℂ) else 0) -
            ((1 / 4 : ℂ) * (if k p.1 - k p.2 + 1 = 0 then (Real.pi : ℂ) else 0) +
              (1 / 4 : ℂ) * (if k p.1 - k p.2 - 1 = 0 then (Real.pi : ℂ) else 0))) := by
  simp only [high_gaussian_angle_norm_sq]
  exact
    high_gaussian_angle_sum (s ×ˢ s) (fun p ↦ c p.1 * (starRingEnd ℂ) (c p.2))
      (fun p ↦ k p.1 - k p.2)

/-- Collapse the upper adjacent diagonal in a square of size `N + 1`. -/
private theorem sum_upper_neighbor {A : Type*} [AddCommMonoid A] (N : ℕ) (f : ℕ → ℕ → A) :
    (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), if i + 1 = j then f i j else 0) =
      ∑ i ∈ Finset.range N, f i (i + 1) := by
  simp only [Finset.sum_ite_eq, Finset.mem_range, Nat.add_lt_add_iff_right]
  rw [Finset.sum_range_succ]
  simp only [lt_irrefl, ite_false, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  exact ite_eq_left (Finset.mem_range.mp hi)

/-- The real part of a Gram summand for real coefficients is supported on three diagonals. -/
private theorem real_gram_term (c : ℕ → ℝ) (i j : ℕ) :
    (((c i : ℂ) * (starRingEnd ℂ) (c j : ℂ)) *
          ((1 / 2 : ℂ) * (if (i : ℤ) - (j : ℤ) = 0 then (Real.pi : ℂ) else 0) -
            ((1 / 4 : ℂ) * (if (i : ℤ) - (j : ℤ) + 1 = 0 then (Real.pi : ℂ) else 0) +
              (1 / 4 : ℂ) * (if (i : ℤ) - (j : ℤ) - 1 = 0 then (Real.pi : ℂ) else 0)))).re =
      (if i = j then (Real.pi / 2) * (c i * c j) else 0) -
        ((if i + 1 = j then (Real.pi / 4) * (c i * c j) else 0) +
          (if i = j + 1 then (Real.pi / 4) * (c i * c j) else 0)) := by
  apply Eq.trans _ (Complex.ofReal_re _)
  apply congrArg Complex.re
  simp only [sub_add_eq_add_sub, sub_sub, sub_eq_zero, ← Int.natCast_succ, Int.ofNat_inj,
    Complex.conj_ofReal, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat, apply_ite, Complex.ofReal_zero]
  split_ifs <;> ring

/-- The two neighboring diagonals have the same sum for real coefficients. -/
private theorem sum_lower_neighbor (N : ℕ) (c : ℕ → ℝ) :
    (∑ i ∈ Finset.range (N + 1),
        ∑ j ∈ Finset.range (N + 1), if i = j + 1 then (Real.pi / 4) * (c i * c j) else 0) =
      ∑ i ∈ Finset.range N, (Real.pi / 4) * (c i * c (i + 1)) := by
  rw [Finset.sum_comm]
  simpa only [eq_comm, mul_comm (c _) (c _)] using
    sum_upper_neighbor N (fun i j ↦ (Real.pi / 4) * (c i * c j))

/-- The diagonal collapses to the sum of squares of the coefficients. -/
private theorem sum_main_diagonal (N : ℕ) (c : ℕ → ℝ) :
    (∑ i ∈ Finset.range (N + 1),
        ∑ j ∈ Finset.range (N + 1), if i = j then (Real.pi / 2) * (c i * c j) else 0) =
      (Real.pi / 2) * ∑ i ∈ Finset.range (N + 1), c i ^ 2 := by
  simp only [Finset.sum_ite_eq, Finset.mul_sum, pow_two]
  apply Finset.sum_congr rfl
  intro i hi
  exact ite_eq_left hi

/-- The real Gram integral equals the coefficient norm minus the adjacent products. -/
public theorem high_gaussian_real_angle_gram (N : ℕ) (c : ℕ → ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi,
        Real.sin θ ^ 2 *
          ‖∑ j ∈ Finset.range (N + 1),
                (c j : ℂ) * Complex.exp (2 * ((j : ℤ) : ℂ) * Complex.I * (θ : ℂ))‖ ^
            2) =
      (Real.pi / 2) *
        ((∑ i ∈ Finset.range (N + 1), c i ^ 2) - ∑ i ∈ Finset.range N, c i * c (i + 1)) := by
  have h :=
    high_gaussian_angle_gram (Finset.range (N + 1)) (fun j ↦ (c j : ℂ)) (fun j : ℕ ↦ (j : ℤ))
  simp only [← Complex.ofReal_mul, intervalIntegral.integral_ofReal] at h
  have hr := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.re_sum, real_gram_term, Finset.sum_product,
    Finset.sum_sub_distrib, Finset.sum_add_distrib] at hr
  rw [hr, sum_main_diagonal, sum_upper_neighbor, sum_lower_neighbor, ← Finset.mul_sum]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
