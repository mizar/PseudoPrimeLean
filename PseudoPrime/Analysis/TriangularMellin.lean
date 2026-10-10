/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! # Entire triangular Mellin kernel

The exponential quotient squared extends across zero. Its imaginary-axis
values are nonnegative sinc squares, and its endpoint value is explicit.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The entire triangular Mellin kernel with parameter `a`.
The derivative slope of sinh removes the apparent singularity at zero.
Away from zero this is the square of `(exp(a*s)-exp(-a*s))/s`,
used in the large-index argument of LLS Section 6.2. -/
noncomputable def triangularMellinFunction (a : ℝ) (s : ℂ) : ℂ :=
  (2 * (a : ℂ) * dslope Complex.sinh 0 ((a : ℂ) * s)) ^ 2

/-- The triangular kernel is entire for every real parameter.
Apply removable singularity to the derivative slope of the entire sinh
function, then compose with scaling and square. This supplies holomorphy
for the Mellin-kernel construction. -/
theorem differentiable_triangularMellinFunction (a : ℝ) :
    Differentiable ℂ (triangularMellinFunction a) := by
  have hd : Differentiable ℂ (dslope Complex.sinh 0) :=
    differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope Filter.univ_mem).mpr
        Complex.differentiable_sinh.differentiableOn)
  exact
    ((differentiable_const _).mul (hd.comp ((differentiable_const _).mul differentiable_id))).pow 2

/-- At zero the triangular kernel equals `4*a²`.
The derivative of sinh at zero is one, giving the regularized value
needed on the imaginary integration line. -/
theorem triangularMellinFunction_zero (a : ℝ) :
    triangularMellinFunction a 0 = (2 * (a : ℂ)) ^ 2 := by
  simp only [triangularMellinFunction, mul_zero, dslope_same, Complex.deriv_sinh, Complex.cosh_zero,
    mul_one]

/-- For nonzero parameter and argument, the regularized triangular kernel
agrees with the exponential quotient squared from Section 6.2.
Expand the derivative slope and sinh, then cancel the nonzero parameter.
This connects its entire definition to the paper's formula. -/
theorem triangularMellinFunction_of_ne_zero {a : ℝ} (ha : a ≠ 0) {s : ℂ} (hs : s ≠ 0) :
    triangularMellinFunction a s =
      ((Complex.exp ((a : ℂ) * s) - Complex.exp (-((a : ℂ) * s))) / s) ^ 2 := by
  have han : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  rw [triangularMellinFunction, dslope_of_ne _ (mul_ne_zero han hs)]
  simp only [slope, vsub_eq_sub, Complex.sinh_zero, sub_zero, smul_eq_mul]
  rw [Complex.sinh]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    _ =
        (Complex.exp ((a : ℂ) * s) - Complex.exp (-((a : ℂ) * s))) * s⁻¹ *
          ((2 : ℂ) * (a : ℂ) * (a : ℂ)⁻¹ * 2⁻¹) :=
      by ring
    _ = _ := by
      rw [mul_assoc (2 : ℂ) (a : ℂ) (a : ℂ)⁻¹, mul_inv_cancel₀ han]; norm_num only; ring

/-- For a nonzero parameter, the real endpoint value is four times the
square of `exp(a/2)-exp(-a/2)`. Evaluate the exponential quotient at one half
and use compatibility with real casts. This fixes the coefficient
subtracted in Proposition 6.1. -/
theorem triangularMellinFunction_half {a : ℝ} (ha : a ≠ 0) :
    (triangularMellinFunction a (1 / 2)).re = 4 * (Real.exp (a / 2) - Real.exp (-a / 2)) ^ 2 := by
  rw [triangularMellinFunction_of_ne_zero ha (by norm_num only)]
  have he :
    (Complex.exp ((a : ℂ) * (1 / 2)) - Complex.exp (-((a : ℂ) * (1 / 2)))) / (1 / 2) =
      ((2 * (Real.exp (a / 2) - Real.exp (-a / 2)) : ℝ) : ℂ) := by
    rw [show (a : ℂ) * (1 / 2) = ((a / 2 : ℝ) : ℂ) by
        simp only [Complex.ofReal_div, Complex.ofReal_ofNat]; ring]
    simp only [← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ring_nf
  rw [he, ← Complex.ofReal_pow, Complex.ofReal_re]
  ring

/-- On the imaginary axis, the triangular kernel is the real square
`(2*a*sinc(a*t))²`, for a nonzero parameter. Treat the origin separately
and use sinh on imaginary arguments elsewhere. The nonnegative value
allows its norm integral to be identified with its transform at one. -/
theorem triangularMellinFunction_imaginary {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    triangularMellinFunction a (Complex.I * t) = (((2 * a * Real.sinc (a * t)) ^ 2 : ℝ) : ℂ) := by
  by_cases ht : t = 0
  · subst t
    simp only [Complex.ofReal_zero, mul_zero, triangularMellinFunction_zero, Real.sinc_zero,
      mul_one, Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat]
  · have hn : (a : ℂ) * (Complex.I * (t : ℂ)) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr ha)
        (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht))
    rw [triangularMellinFunction, dslope_of_ne _ hn]
    simp only [slope, vsub_eq_sub, Complex.sinh_zero, sub_zero, smul_eq_mul]
    rw [show (a : ℂ) * (Complex.I * (t : ℂ)) = ((a * t : ℝ) : ℂ) * Complex.I by
        rw [Complex.ofReal_mul]; ring,
      Complex.sinh_mul_I, ← Complex.ofReal_sin]
    rw [Real.sinc_of_ne_zero (mul_ne_zero ha ht)]
    simp only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat,
      div_eq_mul_inv, mul_inv_rev]
    rw [show Complex.I⁻¹ = -Complex.I by exact Complex.inv_I]
    congr 1
    calc
      _ = (2 * (a : ℂ) * (↑(Real.sin (a * t)) * (↑t)⁻¹ * (↑a)⁻¹)) * (-(Complex.I * Complex.I)) := by
        ring
      _ = _ := by
        rw [Complex.I_mul_I, neg_neg, mul_one]; ring

/-- The imaginary-axis norm equals the sinc square for nonzero parameter.
The kernel value is a nonnegative real cast, so taking the norm removes
the cast without an absolute-value sign. This is the mass integrand. -/
theorem norm_triangularMellinFunction_imaginary {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    ‖triangularMellinFunction a (Complex.I * t)‖ = (2 * a * Real.sinc (a * t)) ^ 2 := by
  rw [triangularMellinFunction_imaginary ha, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]

end PseudoPrime.Analysis
