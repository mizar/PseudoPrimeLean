/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundGammaKernel
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Infinite positive Gamma-remainder integral -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A nonnegative locally interval-integrable function whose finite integrals
are bounded is integrable on `(0,∞)`, and its improper integral has the same
bounds. Use bounded norm integrals along the natural-number exhaustion. -/
private theorem integrableOn_Ioi_of_bounded_intervals (f : ℝ → ℝ) (M : ℝ)
    (hi : ∀ R : ℝ, IntervalIntegrable f MeasureTheory.volume 0 R) (hp : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x)
    (hb : ∀ R : ℝ, 0 ≤ R → 0 ≤ (∫ x in (0 : ℝ)..R, f x) ∧ (∫ x in (0 : ℝ)..R, f x) ≤ M) :
    MeasureTheory.IntegrableOn f (Set.Ioi 0) ∧
      0 ≤ (∫ x in Set.Ioi (0 : ℝ), f x) ∧ (∫ x in Set.Ioi (0 : ℝ), f x) ≤ M := by
  have hfi (n : ℕ) : MeasureTheory.IntegrableOn f (Set.Ioc (0 : ℝ) (n : ℝ)) := by
    have h := intervalIntegrable_iff.mp (hi n)
    rwa [Set.uIoc_of_le (Nat.cast_nonneg n)] at h
  have hbound (n : ℕ) : (∫ x in (0 : ℝ)..(n : ℝ), ‖f x‖) ≤ M := by
    have he : (∫ x in (0 : ℝ)..(n : ℝ), ‖f x‖) = ∫ x in (0 : ℝ)..(n : ℝ), f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (Nat.cast_nonneg n)] at hx
      change ‖f x‖ = f x
      rw [Real.norm_eq_abs, abs_of_nonneg (hp x hx.1)]
    rw [he]
    exact (hb n (Nat.cast_nonneg n)).2
  have hInt : MeasureTheory.IntegrableOn f (Set.Ioi 0) :=
    MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded (μ := MeasureTheory.volume)
      (l := Filter.atTop) (b := fun n : ℕ => (n : ℝ)) M 0 hfi tendsto_natCast_atTop_atTop
      (Filter.Eventually.of_forall hbound)
  have ht :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hInt
      (tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop)
  refine ⟨hInt, ?_, ?_⟩
  · exact ge_of_tendsto' ht (fun n => (hb n (Nat.cast_nonneg n)).1)
  · exact le_of_tendsto' ht (fun n => (hb n (Nat.cast_nonneg n)).2)

/-- For `a ≥ 0` and `y > 0`, the positive weighted Gamma kernel is integrable
on `(0,∞)`, and its integral is at most `y/(8(a²+y²))`. The finite-interval
estimate passes to the improper integral through the norm-bound criterion. -/
theorem backlundGammaWeight_integral_Ioi {a y : ℝ} (ha : 0 ≤ a) (hy : 0 < y) :
    MeasureTheory.IntegrableOn (fun x => backlundGammaWeight x * backlundGammaKernel a y x)
        (Set.Ioi 0) ∧
      0 ≤ (∫ x in Set.Ioi (0 : ℝ), backlundGammaWeight x * backlundGammaKernel a y x) ∧
      (∫ x in Set.Ioi (0 : ℝ), backlundGammaWeight x * backlundGammaKernel a y x) ≤
        y / (8 * (a ^ 2 + y ^ 2)) := by
  apply integrableOn_Ioi_of_bounded_intervals
  · intro R
    exact
      (backlundGammaWeight_intervalIntegrable R).mul_continuousOn
        (backlundGammaKernel_continuous a hy).continuousOn
  · intro x hx
    apply mul_nonneg (backlundGammaWeight_bounds x).1
    apply div_nonneg (mul_nonneg hy.le (add_nonneg hx ha))
    exact sq_nonneg _
  · intro R hR
    exact backlundGammaWeight_integral_bounds ha hy hR

/-- At positive height `T`, the Gamma-remainder kernel at `a=1/4` and
`y=T/2` is integrable and its integral lies in `[0,1/(4T)]`. The general
kernel budget and a positive-denominator comparison give the constants. -/
theorem backlundGammaWeight_integral_height {T : ℝ} (hT : 0 < T) :
    MeasureTheory.IntegrableOn
        (fun x => backlundGammaWeight x * backlundGammaKernel (1 / 4) (T / 2) x) (Set.Ioi 0) ∧
      0 ≤ (∫ x in Set.Ioi (0 : ℝ), backlundGammaWeight x * backlundGammaKernel (1 / 4) (T / 2) x) ∧
      (∫ x in Set.Ioi (0 : ℝ), backlundGammaWeight x * backlundGammaKernel (1 / 4) (T / 2) x) ≤
        1 / (4 * T) := by
  have hy : 0 < T / 2 := by linarith only [hT]
  have h := backlundGammaWeight_integral_Ioi (a := 1 / 4) (y := T / 2) (by norm_num only) hy
  refine ⟨h.1, h.2.1, h.2.2.trans ?_⟩
  have hd : 0 < 8 * ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2) :=
    mul_pos (by norm_num only) (add_pos_of_pos_of_nonneg (by norm_num only) (sq_nonneg _))
  apply (div_le_div_iff₀ hd (mul_pos (by norm_num only) hT)).2
  nlinarith only [sq_nonneg T]

end PseudoPrime.PrimeTestBounds.MillerRabin
