/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! # Rational complex arithmetic for finite moment evaluation -/

namespace PseudoPrime.Analysis

/-- A complex number with exact rational real and imaginary coordinates.
The operations below compute the corresponding complex operations on these coordinates. -/
public structure RatComplex where
  /-- The exact real coordinate. -/
  re : ℚ
  /-- The exact imaginary coordinate. -/
  im : ℚ

/-- Embed the two rational coordinates into the complex numbers. -/
@[expose]
public def RatComplex.val (z : RatComplex) : ℂ :=
  ⟨z.re, z.im⟩

/-- Embed a rational on the real axis. -/
@[expose]
public def RatComplex.real (a : ℚ) : RatComplex :=
  ⟨a, 0⟩

/-- Add the real and imaginary coordinates separately. -/
@[expose]
public def RatComplex.add (x y : RatComplex) : RatComplex :=
  ⟨x.re + y.re, x.im + y.im⟩

/-- Multiply using the complex product rule on rational coordinates. -/
@[expose]
public def RatComplex.mul (x y : RatComplex) : RatComplex :=
  ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩

/-- Divide the conjugate by its squared norm, including the convention that zero inverts to zero. -/
@[expose]
public def RatComplex.inv (z : RatComplex) : RatComplex :=
  let d := z.re * z.re + z.im * z.im
  ⟨z.re / d, -z.im / d⟩

/-- The embedding preserves rational real-axis values. -/
public theorem RatComplex.val_real (a : ℚ) : (RatComplex.real a).val = (a : ℂ) := by
  apply Complex.ext
  · exact (Complex.ratCast_re a).symm
  · simp only [RatComplex.val, RatComplex.real, Rat.cast_zero, Complex.ratCast_im]

/-- The embedding preserves addition. -/
public theorem RatComplex.val_add (x y : RatComplex) : (x.add y).val = x.val + y.val := by
  apply Complex.ext <;>
    simp only [RatComplex.val, RatComplex.add, Rat.cast_add, Complex.add_re, Complex.add_im]

/-- The embedding preserves multiplication. -/
public theorem RatComplex.val_mul (x y : RatComplex) : (x.mul y).val = x.val * y.val := by
  apply Complex.ext <;>
    simp only [RatComplex.val, RatComplex.mul, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
      Complex.mul_re, Complex.mul_im]

/-- The embedding preserves reciprocal, with the same totalized division convention. -/
public theorem RatComplex.val_inv (z : RatComplex) : z.inv.val = z.val⁻¹ := by
  apply Complex.ext <;>
    simp only [RatComplex.val, RatComplex.inv, Rat.cast_div, Rat.cast_neg, Rat.cast_add,
      Rat.cast_mul, Complex.inv_re, Complex.inv_im, Complex.normSq_apply, neg_div]

/-- Evaluate the first `n` real coefficients by Horner recursion over rational coordinates. -/
public def RatComplex.horner (c : ℕ → ℚ) (z : RatComplex) : ℕ → RatComplex
  | 0 => RatComplex.real 0
  | n + 1 => (RatComplex.real (c 0)).add (z.mul (RatComplex.horner (fun i ↦ c (i + 1)) z n))

/-- The Horner value embeds as the finite power sum of the rational coefficients. -/
public theorem RatComplex.val_horner (c : ℕ → ℚ) (z : RatComplex) (n : ℕ) :
    (RatComplex.horner c z n).val = ∑ i ∈ Finset.range n, (c i : ℂ) * z.val ^ i := by
  induction n generalizing c with
  | zero =>
    simp only [RatComplex.horner, RatComplex.val_real, Rat.cast_zero, Finset.range_zero,
      Finset.sum_empty]
  | succ n
    ih =>
    rw [RatComplex.horner, RatComplex.val_add, RatComplex.val_mul, RatComplex.val_real, ih,
      Finset.sum_range_succ', Finset.mul_sum, add_comm]
    simp only [pow_zero, mul_one]
    apply congrArg (· + (c 0 : ℂ))
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring

/-- The exact squared norm of the two rational coordinates. -/
@[expose]
public def RatComplex.normSq (z : RatComplex) : ℚ :=
  z.re ^ 2 + z.im ^ 2

/-- A rational comparison of squared norms certifies an upper bound on the complex norm. -/
public theorem RatComplex.val_norm_le (z : RatComplex) {b : ℚ} (hb : 0 ≤ b) (h : z.normSq ≤ b ^ 2) :
    ‖z.val‖ ≤ (b : ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Rat.cast_nonneg.mpr hb)).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  have he := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [RatComplex.normSq, RatComplex.val, pow_two, Rat.cast_add, Rat.cast_mul] using he

end PseudoPrime.Analysis
