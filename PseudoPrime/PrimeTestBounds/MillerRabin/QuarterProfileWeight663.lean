/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfileBernstein663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel656

/-! # Common Euler inequality in the physical weight -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Multiplying the normalized forward profile by the common inverse
power recovers the physical kernel weight at positive radius and argument. -/
theorem quarter_forward_weight_663 {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    t ^ (-(8 / 5) : ℝ) * quarterForward663 r (Real.log (t / r ^ 2)) =
      quarterWeight656 (r ^ 2) t := by
  let u := Real.log (t / r ^ 2)
  have hu : u = Real.log t - 2 * Real.log r := by
    dsimp only [u]
    rw [Real.log_div ht.ne' (pow_ne_zero _ hr.ne'), Real.log_pow, Nat.cast_ofNat]
  have he :
    t ^ (-(8 / 5) : ℝ) * Real.exp (-(231 / 80)) * r ^ (11 / 5 : ℝ) * Real.exp ((11 / 5) * u) =
      (1 / Real.sqrt t) * Real.exp (-((11 / 10) * (21 / 8 - u))) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht, Real.rpow_def_of_pos ht,
      Real.rpow_def_of_pos hr, one_div, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, ←
      Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hu]
    ring
  unfold quarterForward663 quarterWeight656
  dsimp only
  change
    _ *
        ((11 / 10) ^ 5 * Real.exp (-(231 / 80)) * _ * Real.exp ((11 / 5) * u) * (21 / 8 - u) ^ 5 /
          120) =
      (1 / Real.sqrt t) *
        (((11 / 10) * (21 / 8 - u)) ^ 5 * Real.exp (-((11 / 10) * (21 / 8 - u))) / 120)
  linear_combination ((11 / 10 : ℝ) ^ 5 * (21 / 8 - u) ^ 5 / 120) * he

/-- At a physical argument above the tested cutoff, the common Euler
deficit is bounded with the forward kernel and reflected weight in their
original units. The forward weight is zero beyond its support. -/
theorem quarter_physical_euler_663 {r t a : ℝ} (hr : 328 ≤ r) (ht : r ^ 2 ≤ t)
    (ha : a ∈ Set.Icc 0 4) :
    let f := if Real.log (t / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) t else 0
    let g := t ^ (-(8 / 5) : ℝ) * quarterProfile663 (Real.log t)
    (-4) * g ≤ (4 - a) * f - a * g := by
  intro f g
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 328).trans_le hr
  have hX : 0 < r ^ 2 := sq_pos_of_pos hr₀
  have ht₀ := hX.trans_le ht
  let u := Real.log (t / r ^ 2)
  have hu : 0 ≤ u := Real.log_nonneg ((le_div_iff₀ hX).mpr (by simpa only [one_mul] using ht))
  have hl : 2 * Real.log r + u = Real.log t := by
    dsimp only [u]
    rw [Real.log_div ht₀.ne' hX.ne', Real.log_pow, Nat.cast_ofNat]
    ring
  have hf : t ^ (-(8 / 5) : ℝ) * (if u ≤ 21 / 8 then quarterForward663 r u else 0) = f := by
    dsimp only [f, u]
    rw [mul_ite, mul_zero, quarter_forward_weight_663 hr₀ ht₀]
  have h :=
    mul_le_mul_of_nonneg_left (quarter_profile_euler_663 hr hu ha)
      (Real.rpow_nonneg ht₀.le (-(8 / 5) : ℝ))
  rw [hl] at h
  dsimp only [g]
  linear_combination h + (4 - a) * hf

/-- On a finite part of the unknown support, each Mangoldt weight
preserves the common Euler inequality, with a single trace deficit for
the forward and reflected terms. -/
theorem quarter_euler_tail_sum_663 (s : Finset ℕ) (a : ℕ → ℝ) {r : ℝ} (hr : 328 ≤ r)
    (hs : ∀ n ∈ s, r ^ 2 ≤ (n : ℝ)) (ha : ∀ n ∈ s, a n ∈ Set.Icc 0 4) :
    let f := fun n : ℕ ↦
      if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0
    let g := fun n : ℕ ↦ (n : ℝ) ^ (-(8 / 5) : ℝ) * quarterProfile663 (Real.log n)
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * (-4 * g n)) ≤
      ∑ n ∈ s, ArithmeticFunction.vonMangoldt n * ((4 - a n) * f n - a n * g n) := by
  intro f g
  exact
    Finset.sum_le_sum fun n hn ↦
      mul_le_mul_of_nonneg_left (quarter_physical_euler_663 hr (hs n hn) (ha n hn))
        ArithmeticFunction.vonMangoldt_nonneg

end PseudoPrime.PrimeTestBounds.MillerRabin
