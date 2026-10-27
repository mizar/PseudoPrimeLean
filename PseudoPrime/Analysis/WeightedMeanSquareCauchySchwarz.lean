/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialMeanSquareIntervals
public import PseudoPrime.Analysis.MeanSquareCauchySchwarz

/-! # Cauchy--Schwarz with the Laplace weight -/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- The positive square root of the Laplace weight. It converts weighted L2 into ordinary L2. -/
noncomputable def decay (v : ℝ) : ℝ :=
  Real.exp (-|v|)

/-- The normalized function `exp (-|v|) • f v`; its ordinary squared norm is the energy density. -/
noncomputable def normalize (f : ℝ → ℂ) (v : ℝ) : ℂ :=
  decay v • f v

/-- The square of the positive normalizing scalar is the Laplace weight.
Combine two equal exponentials for the weighted L2 normalization. -/
theorem decay_sq (v : ℝ) : decay v ^ 2 = weight v := by
  rw [decay, pow_two, ← Real.exp_add, weight]
  congr 1
  ring

/-- The normalized norm is the positive decay times the original norm.
Use the real scalar norm and positivity for the mean-square conversion. -/
theorem norm_normalize (f : ℝ → ℂ) (v : ℝ) : ‖normalize f v‖ = decay v * ‖f v‖ := by
  rw [normalize, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ decay v from (Real.exp_pos _).le)]

/-- The ordinary norm square of the normalized function equals its energy density.
Square the norm formula and identify the Laplace weight. -/
theorem norm_normalize_sq (f : ℝ → ℂ) (v : ℝ) : ‖normalize f v‖ ^ 2 = ‖f v‖ ^ 2 * weight v := by
  rw [norm_normalize, mul_pow, decay_sq, mul_comm]

/-- Normalization preserves continuity of a complex function on the real line.
The real exponential decay is continuous and acts by scalar multiplication. -/
theorem continuous_normalize {f : ℝ → ℂ} (hf : Continuous f) : Continuous (normalize f) := by
  exact (Real.continuous_exp.comp continuous_abs.neg).smul hf

/-- A continuous function with integrable energy density normalizes to an actual L2 function.
Use the norm-square criterion with the exact density identity. -/
theorem memLp_normalize {f : ℝ → ℂ} (hf : Continuous f)
    (hi : MeasureTheory.Integrable (fun v ↦ ‖f v‖ ^ 2 * weight v)) :
    MeasureTheory.MemLp (normalize f) 2 := by
  apply
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
        (continuous_normalize hf).aestronglyMeasurable).mpr
  simpa only [norm_normalize_sq] using hi

/-- The product of normalized norms is the weighted product of the original norms.
The two scalar factors multiply to the weight, preserving cross-norm integrals. -/
theorem norm_normalize_mul (f g : ℝ → ℂ) (v : ℝ) :
    ‖normalize f v‖ * ‖normalize g v‖ = ‖f v‖ * ‖g v‖ * weight v := by
  rw [norm_normalize, norm_normalize, ← decay_sq]
  ring

/-- For continuous functions with integrable energy densities, the weighted norm product
integral is bounded by the product of their energy square roots.
Apply Holder after normalization. -/
theorem weighted_norm_mul_le_sqrt {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hi : MeasureTheory.Integrable (fun v ↦ ‖f v‖ ^ 2 * weight v))
    (hj : MeasureTheory.Integrable (fun v ↦ ‖g v‖ ^ 2 * weight v)) :
    (∫ v : ℝ, ‖f v‖ * ‖g v‖ * weight v) ≤ Real.sqrt (energy f) * Real.sqrt (energy g) := by
  have hf' : MeasureTheory.MemLp (normalize f) (ENNReal.ofReal (2 : ℝ)) := by
    simpa only [ENNReal.ofReal_ofNat] using memLp_normalize hf hi
  have hg' : MeasureTheory.MemLp (normalize g) (ENNReal.ofReal (2 : ℝ)) := by
    simpa only [ENNReal.ofReal_ofNat] using memLp_normalize hg hj
  have h := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hg'
  simpa only [norm_normalize_mul, Real.rpow_two, norm_normalize_sq, ← Real.sqrt_eq_rpow,
    energy] using h

/-- For continuous functions with integrable energy densities, the weighted norm product
is integrable. Use L2 Holder on the normalized norms and the exact product identity. -/
theorem integrable_weighted_norm_mul {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hi : MeasureTheory.Integrable (fun v ↦ ‖f v‖ ^ 2 * weight v))
    (hj : MeasureTheory.Integrable (fun v ↦ ‖g v‖ ^ 2 * weight v)) :
    MeasureTheory.Integrable (fun v ↦ ‖f v‖ * ‖g v‖ * weight v) := by
  have h := (memLp_normalize hf hi).norm.integrable_mul (memLp_normalize hg hj).norm
  simpa only [Pi.mul_def, norm_normalize_mul] using h

end PseudoPrime.Analysis.ExponentialMeanSquare
