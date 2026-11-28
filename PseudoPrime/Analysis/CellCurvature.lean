/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # One-sided curvature bounds for closed-cell comparisons -/

namespace PseudoPrime.Analysis

/-- The quadratic chord correction vanishes at the two cell endpoints. -/
private theorem chord_correction_deriv (a b M t : ℝ) :
    HasDerivAt (fun x ↦ (M / 2) * ((x - a) * (b - x))) ((M / 2) * (a + b - 2 * t)) t := by
  have h := (((hasDerivAt_id t).sub_const a).mul ((hasDerivAt_id t).const_sub b)).const_mul (M / 2)
  convert h using 1
  · rfl
  · simp only [id_eq, one_mul]
    ring

/-- The correction is concave after adding it to a function whose
second derivative is at most the curvature cap. -/
private theorem corrected_cell_concave {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (hc : ContinuousOn f (Set.Icc a b)) (h₁ : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (h₂ : ∀ x ∈ Set.Ioo a b, HasDerivAt f' (f'' x) x) (hM : ∀ x ∈ Set.Ioo a b, f'' x ≤ M) :
    ConcaveOn ℝ (Set.Icc a b) (fun x ↦ f x + (M / 2) * ((x - a) * (b - x))) := by
  refine
    concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc a b) (f' := fun x ↦
      f' x + (M / 2) * (a + b - 2 * x)) (f'' := fun x ↦ f'' x + (-M))
      (hc.add fun x _ ↦ (chord_correction_deriv a b M x).continuousAt.continuousWithinAt) ?_ ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact ((h₁ x hx).add (chord_correction_deriv a b M x)).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have h := (((hasDerivAt_id x).const_mul (2 : ℝ)).const_sub (a + b)).const_mul (M / 2)
    have h' : HasDerivAt (fun y ↦ (M / 2) * (a + b - 2 * y)) (-M) x := by
      convert h using 1
      · rfl
      · ring
    exact ((h₂ x hx).add h').hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    linarith only [hM x hx]

/-- Endpoint lower bounds and a one-sided second-derivative cap bound the
entire closed cell. The loss is at most the curvature cap times width squared over eight. -/
public theorem cell_lower_of_curvature {f f' f'' : ℝ → ℝ} {a b M m t : ℝ} (ht : t ∈ Set.Icc a b)
    (hM₀ : 0 ≤ M) (hc : ContinuousOn f (Set.Icc a b))
    (h₁ : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (h₂ : ∀ x ∈ Set.Ioo a b, HasDerivAt f' (f'' x) x) (hM : ∀ x ∈ Set.Ioo a b, f'' x ≤ M)
    (ha : m ≤ f a) (hb : m ≤ f b) : m - M * (b - a) ^ 2 / 8 ≤ f t := by
  have hab := ht.1.trans ht.2
  have hc' := corrected_cell_concave hc h₁ h₂ hM
  have ht' := hc'.min_le_of_mem_Icc ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ ht
  simp only [sub_self, zero_mul, mul_zero, add_zero] at ht'
  have hsq : (t - a) * (b - t) ≤ (b - a) ^ 2 / 4 := by nlinarith only [sq_nonneg (2 * t - a - b)]
  have h := mul_le_mul_of_nonneg_left hsq (div_nonneg hM₀ (by norm_num only : (0 : ℝ) ≤ 2))
  linarith only [(le_min ha hb).trans ht', h]

end PseudoPrime.Analysis
