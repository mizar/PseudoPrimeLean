/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Integrals of exponential absolute-value decay

Splitting at zero proves absolute integrability and the exact integral.
These formulas evaluate finite exponential majorants on the whole real line.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a positive rate the absolute-value exponential is integrable.
Split the real line into its two half-lines and apply exponential convergence.
This supplies integrable majorants for vertical gamma values. -/
theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun t : ℝ ↦ Real.exp (-a * |t|)) := by
  have hl : MeasureTheory.IntegrableOn (fun t : ℝ ↦ Real.exp (-a * |t|)) (Set.Iic 0) := by
    apply
      (MeasureTheory.integrableOn_congr_fun ?_ measurableSet_Iic).mpr
        (integrableOn_exp_mul_Iic ha 0)
    intro t ht
    dsimp only
    rw [abs_of_nonpos (Set.mem_Iic.mp ht)]
    congr 1
    ring
  have hr : MeasureTheory.IntegrableOn (fun t : ℝ ↦ Real.exp (-a * |t|)) (Set.Ioi 0) := by
    apply
      (MeasureTheory.integrableOn_congr_fun ?_ measurableSet_Ioi).mpr
        (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0)
    intro t ht
    dsimp only
    rw [abs_of_pos (Set.mem_Ioi.mp ht)]
  exact MeasureTheory.integrableOn_univ.mp ((Set.Iic_union_Ioi (a := (0 : ℝ))) ▸ hl.union hr)

/-- At positive rate `a`, the integral of `exp(-a*abs(t))` is `2/a`.
Split at zero, integrate each exponential, and add the equal contributions.
This evaluates the terms of gamma-mass polynomial majorants. -/
theorem integral_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) : (∫ t : ℝ, Real.exp (-a * |t|)) = 2 / a := by
  have hi := integrable_exp_neg_mul_abs ha
  have hleft :
    (∫ t : ℝ in Set.Iic 0, Real.exp (-a * |t|)) = ∫ t : ℝ in Set.Iic 0, Real.exp (a * t) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro t ht
    dsimp only
    rw [abs_of_nonpos (Set.mem_Iic.mp ht)]
    congr 1
    ring
  have hright :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-a * |t|)) = ∫ t : ℝ in Set.Ioi 0, Real.exp (-a * t) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [abs_of_pos (Set.mem_Ioi.mp ht)]
  have hd : Disjoint (Set.Iic (0 : ℝ)) (Set.Ioi 0) := by
    apply Set.disjoint_left.mpr
    intro t ht hl
    exact (not_le_of_gt (Set.mem_Ioi.mp hl)) (Set.mem_Iic.mp ht)
  rw [← MeasureTheory.setIntegral_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)),
    MeasureTheory.setIntegral_union hd measurableSet_Ioi hi.integrableOn hi.integrableOn, hleft,
    hright, integral_exp_mul_Iic ha 0, integral_exp_mul_Ioi (neg_neg_of_pos ha) 0, mul_zero,
    mul_zero, Real.exp_zero, neg_div_neg_eq]
  ring

/-- Hyperbolic cosine times twice the decaying exponential equals
`1+exp(-2*abs(x))`. The exponential addition formula proves the identity.
It converts reflection to an inverse-square-root comparison. -/
theorem cosh_mul_twice_exp_neg (x : ℝ) :
    Real.cosh x * (2 * Real.exp (-|x|)) = 1 + Real.exp (-2 * |x|) := by
  have he : Real.exp |x| * Real.exp (-|x|) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsq : Real.exp (-|x|) * Real.exp (-|x|) = Real.exp (-2 * |x|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← Real.cosh_abs, Real.cosh_eq]
  calc
    _ = Real.exp |x| * Real.exp (-|x|) + Real.exp (-|x|) * Real.exp (-|x|) := by ring
    _ = _ := by rw [he, hsq]

end PseudoPrime.Analysis
