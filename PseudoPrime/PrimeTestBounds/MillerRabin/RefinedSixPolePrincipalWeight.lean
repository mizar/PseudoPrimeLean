/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleMass
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Principal weight and second Abel density of the refined kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The positive-support logarithmic coordinate for the refined profile, used in its
principal weight and its derivatives. -/
noncomputable def refinedCoord (u : ℝ) : ℝ :=
  567 / 200 - (27 / 25) * Real.log u

/-- The algebraic continuation of the normalized principal weight. On the positive
support it equals the actual inverse-Mellin profile divided by the square root. -/
noncomputable def refinedWeight (u : ℝ) : ℝ :=
  refinedCoord u ^ 5 * Real.exp (-refinedCoord u) / (120 * Real.sqrt u)

/-- The explicit first derivative of the principal weight at positive arguments.
It supplies the boundary term for finite double Abel summation. -/
noncomputable def refinedWeightDeriv (u : ℝ) : ℝ :=
  Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) *
    ((29 / 50 : ℝ) * refinedCoord u ^ 5 - (27 / 5 : ℝ) * refinedCoord u ^ 4)

/-- The signed second Abel density, the derivative of the argument times the first
weight derivative. Its logarithmic moments control the principal-sum error. -/
noncomputable def refinedSecondDensity (u : ℝ) : ℝ :=
  Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) *
    ((29 / 50 : ℝ) ^ 2 * refinedCoord u ^ 5 -
        10 * (29 / 50 : ℝ) * (27 / 25 : ℝ) * refinedCoord u ^ 4 +
      20 * (27 / 25 : ℝ) ^ 2 * refinedCoord u ^ 3)

/-- At a positive argument the coordinate has its logarithmic derivative. Apply
the derivative of the real logarithm and normalize the rational coefficient. -/
theorem refinedCoord_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt refinedCoord (-(27 / 25 : ℝ) / u) u := by
  have h :=
    (hasDerivAt_const u (567 / 200 : ℝ)).sub ((Real.hasDerivAt_log hu.ne').const_mul (27 / 25 : ℝ))
  convert h using 1
  · rfl
  · ring

/-- The refined principal weight has its displayed derivative for positive arguments.
Differentiate the coordinate, exponential and square root and normalize denominators. -/
theorem refinedWeight_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt refinedWeight (refinedWeightDeriv u) u := by
  have hv := refinedCoord_hasDerivAt hu
  have hs : Real.sqrt u ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  have h :=
    ((hv.pow 5).mul hv.neg.exp).div ((Real.hasDerivAt_sqrt hu.ne').const_mul 120)
      (mul_ne_zero (by norm_num only) hs)
  convert h using 1
  · rfl
  · dsimp only [refinedWeightDeriv, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat]
    field_simp (disch :=
      first
      | exact hu.ne'
      | exact hs
      | norm_num only)
    rw [Real.sq_sqrt hu.le]
    ring

/-- At positive arguments the derivative of the argument times the weight derivative
is the second Abel density. Differentiate the explicit formula and simplify. -/
theorem refinedWeight_log_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun t ↦ t * refinedWeightDeriv t) (refinedSecondDensity u) u := by
  have hv := refinedCoord_hasDerivAt hu
  have hs := (Real.sqrt_pos.mpr hu).ne'
  have hd := ((hasDerivAt_id u).const_mul 120).mul (Real.hasDerivAt_sqrt hu.ne')
  have hp := ((hv.pow 5).const_mul (29 / 50 : ℝ)).sub ((hv.pow 4).const_mul (27 / 5 : ℝ))
  have h :=
    (hasDerivAt_id u).mul
      ((hv.neg.exp.div hd (mul_ne_zero (mul_ne_zero (by norm_num only) hu.ne') hs)).mul hp)
  apply h.congr_deriv
  dsimp only [refinedSecondDensity, Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply,
    Pi.neg_apply, id_eq]
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
  field_simp (disch :=
    first
    | exact hu.ne'
    | exact hs
    | norm_num only)
  rw [Real.sq_sqrt hu.le]
  ring

/-- On the positive support, the actual normalized kernel weight is the algebraic
weight. Specialize rational-pole inversion and identify its logarithmic coordinate. -/
theorem refinedKernelWeight_eq {u : ℝ} (hu : 0 < u) (hl : Real.log u ≤ 21 / 8) :
    (refinedSixPoleKernel.transform u).re / Real.sqrt u = refinedWeight u := by
  rw [refinedSixPoleKernel,
    LLS.PaperStatements.rationalPole_transform (m := 3) (a := 25 / 54) (c := 21 / 16) (u := u)
      (by norm_num only) (by norm_num only) (by norm_num only) hu,
    Complex.ofReal_re, Analysis.rationalPoleProfile]
  have ha : 0 < u ∧ Real.log u ≤ 2 * (21 / 16 : ℝ) := ⟨hu, by linarith only [hl]⟩
  rw [ite_eq_left ha]
  have he : (2 * (21 / 16 : ℝ) - Real.log u) / (2 * (25 / 54 : ℝ)) = refinedCoord u := by
    dsimp only [refinedCoord]
    ring
  norm_num only [Nat.reduceMul, Nat.reduceSub, Nat.factorial, Nat.cast_ofNat]
  norm_num only at he
  rw [he]
  dsimp only [refinedWeight]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
