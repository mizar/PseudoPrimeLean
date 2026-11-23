/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Explicit high-order Taylor quadrature -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- On an ordered compact interval, integrating the degree-`n` Taylor
polynomial incurs at most `C * (b-a)^(n+2) / n!` if the `(n+1)`-st
within-derivative has norm at most `C`. This supports high-order validated
quadrature when low-order midpoint errors are too large. -/
theorem taylor_integral_error_bound {f : ℝ → ℂ} {a b C : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Set.Icc a b))
    (hC : ∀ y ∈ Set.Icc a b, ‖iteratedDerivWithin (n + 1) f (Set.Icc a b) y‖ ≤ C) :
    ‖(∫ x in a..b, f x) - ∫ x in a..b, taylorWithinEval f n (Set.Icc a b) a x‖ ≤
      C * (b - a) ^ (n + 2) / n.factorial := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC a ⟨le_rfl, hab⟩)
  have hw : 0 ≤ b - a := sub_nonneg.mpr hab
  have hfint : IntervalIntegrable f MeasureTheory.volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hf.continuousOn
  have hpol : Continuous (taylorWithinEval f n (Set.Icc a b) a) := by
    cases n with
    | zero =>
      have he : taylorWithinEval f 0 (Set.Icc a b) a = fun _ ↦ f a := by
        funext x
        exact taylor_within_zero_eval f (Set.Icc a b) a x
      rw [he]
      exact continuous_const
    | succ
      k =>
      have hd : Differentiable ℝ (taylorWithinEval f (k + 1) (Set.Icc a b) a) := by
        intro x
        exact (hasDerivAt_taylorWithinEval_succ f k).differentiableAt
      exact hd.continuous
  have hpint : IntervalIntegrable (taylorWithinEval f n (Set.Icc a b) a) MeasureTheory.volume a b :=
    hpol.intervalIntegrable a b
  rw [← intervalIntegral.integral_sub hfint hpint]
  have hbound :
    ∀ x ∈ Set.uIoc a b,
      ‖f x - taylorWithinEval f n (Set.Icc a b) a x‖ ≤ C * (b - a) ^ (n + 1) / n.factorial := by
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      rw [Set.uIoc_of_le hab] at hx
      exact ⟨hx.1.le, hx.2⟩
    have hm := taylor_mean_remainder_bound hf hx' hC
    have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hx'.1) (sub_le_sub_right hx'.2 a) (n + 1)
    have hmul := mul_le_mul_of_nonneg_left hpow hC0
    exact hm.trans (div_le_div_of_nonneg_right hmul (Nat.cast_nonneg _))
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [abs_of_nonneg hw] at hi
  calc
    _ ≤ (C * (b - a) ^ (n + 1) / n.factorial) * (b - a) := hi
    _ = _ := by
      rw [pow_add]; ring

/-- The integral of a shifted monomial times a fixed complex coefficient is
an explicit scalar multiple of that coefficient. This supplies the exact
term used when integrating a Taylor polynomial. -/
theorem integral_shifted_taylor_term (a b : ℝ) (k : ℕ) (c : ℂ) :
    (∫ x in a..b, (((k.factorial : ℝ)⁻¹ * (x - a) ^ k) : ℝ) • c) =
      (((k.factorial : ℝ)⁻¹ * ((b - a) ^ (k + 1) / (k + 1))) : ℝ) • c := by
  have hp : (∫ x in a..b, (x - a) ^ k) = (b - a) ^ (k + 1) / (k + 1) := by
    rw [intervalIntegral.integral_comp_sub_right (f := fun x : ℝ ↦ x ^ k) a, integral_pow]
    simp only [sub_self, zero_pow (Nat.succ_ne_zero k), sub_zero]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_const_mul, hp]

/-- Integrating a Taylor polynomial over `[a,b]` equals a finite sum of
the endpoint derivatives with explicit monomial weights. This identity
turns the high-order error theorem into a finite quadrature interface. -/
theorem integral_taylor_polynomial (f : ℝ → ℂ) (n : ℕ) (a b : ℝ) :
    (∫ x in a..b, taylorWithinEval f n (Set.Icc a b) a x) =
      ∑ k ∈ Finset.range (n + 1),
        (((k.factorial : ℝ)⁻¹ * ((b - a) ^ (k + 1) / (k + 1))) : ℝ) •
          iteratedDerivWithin k f (Set.Icc a b) a := by
  simp_rw [taylor_within_apply]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    exact integral_shifted_taylor_term a b k (iteratedDerivWithin k f (Set.Icc a b) a)
  · intro k hk
    have hc :
      Continuous
        (fun x : ℝ ↦
          ((k.factorial : ℝ)⁻¹ * (x - a) ^ k) • iteratedDerivWithin k f (Set.Icc a b) a) :=
      (continuous_const.mul ((continuous_id.sub continuous_const).pow k)).smul continuous_const
    exact hc.intervalIntegrable a b

/-- The finite Taylor quadrature sum on an interval uses the within-set
derivatives at the left endpoint and exact integrated monomial weights. -/
noncomputable def taylorCellSum (f : ℝ → ℂ) (n : ℕ) (a b : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    (((k.factorial : ℝ)⁻¹ * ((b - a) ^ (k + 1) / (k + 1))) : ℝ) •
      iteratedDerivWithin k f (Set.Icc a b) a

/-- On a nondegenerate cell, sufficiently smooth endpoint derivatives within
the cell equal ordinary iterated derivatives. This supplies the form needed
for explicit evaluation of the finite quadrature coefficients. -/
theorem taylor_cell_sum_eq_derivatives {f : ℝ → ℂ} {n : ℕ} {a b : ℝ} (hab : a < b)
    (hf : ∀ k ≤ n, ContDiffAt ℝ k f a) :
    taylorCellSum f n a b =
      ∑ k ∈ Finset.range (n + 1),
        (((k.factorial : ℝ)⁻¹ * ((b - a) ^ (k + 1) / (k + 1))) : ℝ) • iteratedDeriv k f a := by
  unfold taylorCellSum
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
      (hf k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))) ⟨le_rfl, hab.le⟩]

/-- The explicit finite Taylor quadrature sum approximates the integral on
one ordered cell with the stated high-order derivative error. -/
theorem taylor_cell_sum_error {f : ℝ → ℂ} {a b C : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Set.Icc a b))
    (hC : ∀ y ∈ Set.Icc a b, ‖iteratedDerivWithin (n + 1) f (Set.Icc a b) y‖ ≤ C) :
    ‖(∫ x in a..b, f x) - taylorCellSum f n a b‖ ≤ C * (b - a) ^ (n + 2) / n.factorial := by
  have h := taylor_integral_error_bound hab hf hC
  rw [integral_taylor_polynomial] at h
  exact h

/-- A finite ordered partition combines the high-order cell quadrature
errors by the triangle inequality. Each cell may have its own derivative
bound, while the Taylor order is common to all cells. -/
theorem taylor_composite_sum_error {f : ℝ → ℂ} {p C : ℕ → ℝ} {n m : ℕ}
    (hab : ∀ j < m, p j ≤ p (j + 1))
    (hf : ∀ j < m, ContDiffOn ℝ (n + 1) f (Set.Icc (p j) (p (j + 1))))
    (hC :
      ∀ j < m,
        ∀ y ∈ Set.Icc (p j) (p (j + 1)),
          ‖iteratedDerivWithin (n + 1) f (Set.Icc (p j) (p (j + 1))) y‖ ≤ C j) :
    ‖(∫ x in p 0..p m, f x) - ∑ j ∈ Finset.range m, taylorCellSum f n (p j) (p (j + 1))‖ ≤
      ∑ j ∈ Finset.range m, C j * (p (j + 1) - p j) ^ (n + 2) / n.factorial := by
  have hi : ∀ j < m, IntervalIntegrable f MeasureTheory.volume (p j) (p (j + 1)) := by
    intro j hj
    exact ContinuousOn.intervalIntegrable_of_Icc (hab j hj) (hf j hj).continuousOn
  calc
    _ =
        ‖∑ j ∈ Finset.range m,
            ((∫ x in p j..p (j + 1), f x) - taylorCellSum f n (p j) (p (j + 1)))‖ :=
      by rw [Finset.sum_sub_distrib, intervalIntegral.sum_integral_adjacent_intervals hi]
    _ ≤
        ∑ j ∈ Finset.range m,
          ‖(∫ x in p j..p (j + 1), f x) - taylorCellSum f n (p j) (p (j + 1))‖ :=
      norm_sum_le _ _
    _ ≤ _ :=
      Finset.sum_le_sum
        (fun j hj ↦
          taylor_cell_sum_error (hab j (Finset.mem_range.mp hj)) (hf j (Finset.mem_range.mp hj))
            (hC j (Finset.mem_range.mp hj)))

end PseudoPrime.Analysis
