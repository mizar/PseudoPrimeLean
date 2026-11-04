/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith

/-! # Prime-count lower bounds from the Chebyshev function

Retain a positive part of the Abel-summation integral when a lower bound for theta holds on a
terminal interval. The estimates are independent of the source of that lower bound.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- If `2 ≤ Y ≤ B` and `η * t ≤ theta t` on `[Y, B]`, the Abel-summation integral
from `2` to `B` is at least `(B - Y) * η / log B ^ 2`. The earlier part is nonnegative,
and monotonicity of the logarithm supplies a constant lower bound on the terminal interval.
This retains a positive secondary term in prime-count estimates. -/
theorem theta_integral_lower {B Y η : ℝ} (hY : 2 ≤ Y) (hYB : Y ≤ B)
    (hθ : ∀ t ∈ Set.Icc Y B, η * t ≤ Chebyshev.theta t) :
    (B - Y) * (η / Real.log B ^ 2) ≤
      ∫ t in (2 : ℝ)..B, Chebyshev.theta t / (t * Real.log t ^ 2) := by
  let f := fun t : ℝ ↦ Chebyshev.theta t / (t * Real.log t ^ 2)
  have hIB := Chebyshev.integrableOn_theta_div_id_mul_log_sq B
  have hI1 : IntervalIntegrable f MeasureTheory.volume 2 Y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hY).mpr
      (hIB.mono_set (Set.Icc_subset_Icc le_rfl hYB))
  have hI2 : IntervalIntegrable f MeasureTheory.volume Y B :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hYB).mpr
      (hIB.mono_set (Set.Icc_subset_Icc hY le_rfl))
  have hi1 : 0 ≤ ∫ t in (2 : ℝ)..Y, f t := by
    apply intervalIntegral.integral_nonneg hY
    intro t ht
    exact div_nonneg (Chebyshev.theta_nonneg t) (mul_nonneg (by linarith only [ht.1]) (sq_nonneg _))
  have hi2 : (B - Y) * (η / Real.log B ^ 2) ≤ ∫ t in Y..B, f t := by
    have hi :=
      intervalIntegral.integral_mono_on hYB intervalIntegrable_const hI2 (f := fun _ ↦
        η / Real.log B ^ 2) (g := f)
        (by
          intro t ht
          have ht0 : 0 < t := by linarith only [hY, ht.1]
          have hlt : 1 < t := by linarith only [hY, ht.1]
          have hl0 : 0 < Real.log t := Real.log_pos hlt
          have hl := Real.log_le_log ht0 ht.2
          have hlsq := pow_le_pow_left₀ hl0.le hl 2
          have hηt : η ≤ Chebyshev.theta t / t := (le_div_iff₀ ht0).mpr (hθ t ht)
          have hh :=
            div_le_div₀ (div_nonneg (Chebyshev.theta_nonneg t) ht0.le) hηt (pow_pos hl0 2) hlsq
          simpa only [f, div_div] using hh)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hi
  have he := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  linarith only [hi1, hi2, he]

/-- Suppose `2 ≤ Y ≤ B`, `a * B ≤ theta B`, and `η * t ≤ theta t` for
`t ∈ [Y, B]`. Abel summation gives the displayed prime-count lower bound with its positive
integral contribution. Combine the endpoint estimate with `theta_integral_lower`.
The parameters allow callers to supply explicit theta estimates on any terminal interval. -/
theorem primeCount_ge_of_theta {B Y a η : ℝ} (hY : 2 ≤ Y) (hYB : Y ≤ B)
    (hθB : a * B ≤ Chebyshev.theta B) (hθ : ∀ t ∈ Set.Icc Y B, η * t ≤ Chebyshev.theta t) :
    (a * B) / Real.log B + (B - Y) * (η / Real.log B ^ 2) ≤ (⌊B⌋₊.primeCounting : ℝ) := by
  have hB : 1 < B := by linarith only [hY, hYB]
  have hl : 0 ≤ Real.log B := (Real.log_pos hB).le
  have hterm := div_le_div_of_nonneg_right hθB hl
  have hi := theta_integral_lower hY hYB hθ
  have he :=
    Chebyshev.primeCounting_eq_theta_div_log_add_integral (show 2 ≤ B by linarith only [hY, hYB])
  linarith only [hterm, hi, he]

/-- For a natural `B ≥ 32`, an endpoint theta lower bound with coefficient `a` and a
uniform lower bound with coefficient `η` on `[B / 16, B]` give the displayed prime-count
bound. Specialize the general Abel estimate and simplify the interval length. The explicit
`15 * η / 16` term can strengthen a prime-supply budget. -/
theorem primeCount_ge_of_theta_sixteenth {B : ℕ} {a η : ℝ} (hB : 32 ≤ B)
    (hθB : a * B ≤ Chebyshev.theta B)
    (hθ : ∀ t ∈ Set.Icc ((B : ℝ) / 16) B, η * t ≤ Chebyshev.theta t) :
    (B : ℝ) * (a / Real.log B + (15 * η / 16) / Real.log B ^ 2) ≤ B.primeCounting := by
  have hBr : (32 : ℝ) ≤ B := Nat.cast_le.mpr hB
  have hY : 2 ≤ (B : ℝ) / 16 := by linarith only [hBr]
  have hYB : (B : ℝ) / 16 ≤ B := by linarith only [hBr]
  have h := primeCount_ge_of_theta hY hYB hθB hθ
  rw [Nat.floor_natCast] at h
  have he :
    (a * (B : ℝ)) / Real.log B + ((B : ℝ) - B / 16) * (η / Real.log B ^ 2) =
      B * (a / Real.log B + (15 * η / 16) / Real.log B ^ 2) := by
    ring
  rw [he] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.Arithmetic
