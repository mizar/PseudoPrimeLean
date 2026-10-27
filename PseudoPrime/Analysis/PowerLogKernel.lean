/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampLogKernel
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Logarithmic double partial summation for real power weights -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At a positive point, the power weight t to the minus sigma has
derivative minus sigma times t to the minus sigma minus one.
This is the first derivative input for double partial summation. -/
theorem powerWeight_derivative (σ : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun t : ℝ ↦ t ^ (-σ)) (-σ * u ^ (-σ - 1)) u := by
  exact Real.hasDerivAt_rpow_const (Or.inl hu.ne')

/-- At a positive point, the derivative of t times the power-weight
derivative equals sigma squared times t to the minus sigma minus one.
Keep the exact power relation before combining the product-rule terms. -/
theorem powerWeight_variation (σ : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun t : ℝ ↦ t * (-σ * t ^ (-σ - 1))) (σ ^ 2 * u ^ (-σ - 1)) u := by
  have h :=
    (hasDerivAt_id u).mul
      ((Real.hasDerivAt_rpow_const (p := -σ - 1) (Or.inl hu.ne')).const_mul (-σ))
  apply h.congr_deriv
  simp only [id_eq]
  rw [Real.rpow_sub_one hu.ne' (-σ - 1)]
  field_simp (discharger := exact hu.ne')
  ring

/-- For a positive reference and interval, the power logarithmic kernel
integrates to both exact boundary terms. Apply the generic logarithmic
variation identity with the two power derivatives and local continuity.
This is the smooth finite identity needed before the infinite Euler tail. -/
theorem power_log_variation_integral (σ : ℝ) {v a b : ℝ} (hv : 0 < v) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log (t / v) * (σ ^ 2 * t ^ (-σ - 1))) =
      Real.log (b / v) * (b * (-σ * b ^ (-σ - 1))) - b ^ (-σ) -
        (Real.log (a / v) * (a * (-σ * a ^ (-σ - 1))) - a ^ (-σ)) := by
  apply
    log_variation_integral hv ha hab (fun u hu ↦ powerWeight_derivative σ (ha.trans_le hu.1))
      (fun u hu ↦ powerWeight_variation σ (ha.trans_le hu.1))
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  have hl : ContinuousOn (fun u : ℝ ↦ Real.log (u / v)) (Set.Icc a b) := fun u hu ↦
    (log_div_derivative hv (ha.trans_le hu.1)).continuousAt.continuousWithinAt
  exact
    hl.mul
      (continuousOn_const.mul
        (fun u hu ↦
          (Real.continuousAt_rpow_const u (-σ - 1)
              (Or.inl (ha.trans_le hu.1).ne')).continuousWithinAt))

/-- On a positive interval, evaluate the logarithmic power kernel by its two
explicit endpoints. Cancel the derivative's extra inverse power. This is
the scalar atom integral used in finite partial summation. -/
theorem power_log_integral_eq (σ : ℝ) {v a b : ℝ} (hv : 0 < v) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log (t / v) * (σ ^ 2 * t ^ (-σ - 1))) =
      a ^ (-σ) * (1 + σ * Real.log (a / v)) - b ^ (-σ) * (1 + σ * Real.log (b / v)) := by
  rw [power_log_variation_integral σ hv ha hab, Real.rpow_sub_one ha.ne' (-σ),
    Real.rpow_sub_one (ha.trans_le hab).ne' (-σ)]
  field_simp (discharger :=
    first
    | exact ha.ne'
    | exact (ha.trans_le hab).ne')
  ring

/-- The clipped logarithmic power kernel is integrable on a positive
finite interval. The clipped logarithm is continuous, and positive inputs
avoid the singularity of a negative real power. -/
theorem intervalIntegrable_power_clipped_kernel (σ : ℝ) {v a b : ℝ} (hv : 0 < v) (ha : 0 < a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ positiveLogRatio v t * (σ ^ 2 * t ^ (-σ - 1))) MeasureTheory.volume
      a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact
    (positiveLogRatio_continuous hv).continuousOn.mul
      (continuousOn_const.mul
        (fun t ht ↦
          (Real.continuousAt_rpow_const t (-σ - 1)
              (Or.inl (ha.trans_le ht.1).ne')).continuousWithinAt))

/-- A positive atom through the upper cutoff has an exact clipped power
integral from a positive lower cutoff. Split at the atom when necessary;
its lower contribution is zero, and the remaining smooth integral has
both endpoints. This includes atoms exactly at the lower cutoff. -/
theorem clipped_power_log_integral_eq (σ : ℝ) {v a b : ℝ} (hv : 0 < v) (ha : 0 < a) (hab : a ≤ b)
    (hvb : v ≤ b) :
    (∫ t in a..b, positiveLogRatio v t * (σ ^ 2 * t ^ (-σ - 1))) =
      (max a v) ^ (-σ) * (1 + σ * Real.log (max a v / v)) -
        b ^ (-σ) * (1 + σ * Real.log (b / v)) := by
  by_cases hva : v ≤ a
  · rw [max_eq_left hva]
    have he :
      (∫ t in a..b, positiveLogRatio v t * (σ ^ 2 * t ^ (-σ - 1))) =
        ∫ t in a..b, Real.log (t / v) * (σ ^ 2 * t ^ (-σ - 1)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      dsimp only
      rw [positiveLogRatio_eq_log (hva.trans ht.1)]
    rw [he, power_log_integral_eq σ hv ha hab]
  · have hav := (lt_of_not_ge hva).le
    rw [max_eq_right hav, ←
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_power_clipped_kernel σ hv ha hav)
        (intervalIntegrable_power_clipped_kernel σ hv hv hvb)]
    have hz : (∫ t in a..v, positiveLogRatio v t * (σ ^ 2 * t ^ (-σ - 1))) = 0 := by
      calc
        _ = ∫ t in a..v, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le hav] at ht
          dsimp only
          rw [positiveLogRatio_zero ht.2, zero_mul]
        _ = 0 := intervalIntegral.integral_zero
    have he :
      (∫ t in v..b, positiveLogRatio v t * (σ ^ 2 * t ^ (-σ - 1))) =
        ∫ t in v..b, Real.log (t / v) * (σ ^ 2 * t ^ (-σ - 1)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hvb] at ht
      dsimp only
      rw [positiveLogRatio_eq_log ht.1]
    rw [hz, zero_add, he, power_log_integral_eq σ hv hv hvb]

/-- A finite weighted sum of positive atoms through b has an exact power
logarithmic integral. Interchange the finite sum and integral with proved
integrability, retaining both cutoff endpoints and all coefficient signs.
This is the finite arithmetic interface for the common resolvent weight. -/
theorem finite_sum_power_log_integral_eq {ι : Type*} (S : Finset ι) (c v : ι → ℝ) (σ : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hv : ∀ i ∈ S, 0 < v i) (hvb : ∀ i ∈ S, v i ≤ b) :
    (∫ t in a..b, (∑ i ∈ S, c i * positiveLogRatio (v i) t) * (σ ^ 2 * t ^ (-σ - 1))) =
      ∑ i ∈ S,
        c i *
          ((max a (v i)) ^ (-σ) * (1 + σ * Real.log (max a (v i) / v i)) -
            b ^ (-σ) * (1 + σ * Real.log (b / v i))) := by
  simp only [Finset.sum_mul, mul_assoc]
  rw [intervalIntegral.integral_finsetSum
      (fun i hi ↦ (intervalIntegrable_power_clipped_kernel σ (hv i hi) ha hab).const_mul (c i))]
  simp only [intervalIntegral.integral_const_mul]
  exact
    Finset.sum_congr rfl
      (fun i hi ↦
        congrArg (fun z : ℝ ↦ c i * z)
          (clipped_power_log_integral_eq σ (hv i hi) ha hab (hvb i hi)))

end PseudoPrime.Analysis
