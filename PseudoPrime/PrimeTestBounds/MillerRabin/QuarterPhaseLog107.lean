/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseClosed107
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightedMoments
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightedEuler
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftReflected

/-! # Logarithmic coordinates for the section 107 phase remainder -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The degree-five reflected main polynomial at log cutoff x. -/
@[expose]
noncomputable def phaseRefMainPoly107 (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 6,
    (Nat.choose 5 k : ℝ) * (x - 1 / 5) ^ (5 - k) * Analysis.logPowerTailPoly (13 / 25) k x

/-- The reflected error polynomial includes the boundary and slope moments. -/
@[expose]
noncomputable def phaseRefErrorPoly107 (x : ℝ) : ℝ :=
  x ^ 2 / 24 * (2 * x - 1 / 5) ^ 5 +
    ∑ k ∈ Finset.range 6,
      twoShiftSlopeCoeff (x - 1 / 5) k * Analysis.logPowerTailPoly (51 / 50) (k + 2) x

/-- In the log-cutoff coordinate the closed reflected tail consists of the
degree-five main polynomial and the degree-seven error polynomial. -/
theorem phase_reflected_log107 {t : ℝ} (ht : 0 < t) :
    phaseReflectedCap107 t =
      Real.exp (-(77 / 50) * Real.log t) * phaseRefMainPoly107 (Real.log t) +
        Real.exp (-(51 / 25) * Real.log t) * phaseRefErrorPoly107 (Real.log t) := by
  unfold phaseReflectedCap107 phaseRefMainPoly107 phaseRefErrorPoly107 twoShiftReflectedDensity
  simp_rw [forward_moment_scale ht, Real.rpow_def_of_pos ht, mul_comm (Real.log t) (-(38 / 25 : ℝ))]
  have hb := forward_boundary_scale ht
  have hmain :
    Real.exp (-(77 / 50 : ℝ) * Real.log t) =
      Real.exp (-(51 / 50) * Real.log t) * Real.exp (-(13 / 25) * Real.log t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have herr :
    Real.exp (-(51 / 25 : ℝ) * Real.log t) =
      Real.exp (-(51 / 50) * Real.log t) * Real.exp (-(51 / 50) * Real.log t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hmain, herr, ← hb]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- The signed coefficient multiplying the two reflected polynomials. -/
@[expose]
noncomputable def phaseRefCoeff107 : ℝ :=
  4 * ((91 / 200 : ℝ) - (11 / 25) * Real.exp (-(51 / 50) * (1 / 5))) *
    ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * (1 / 5)))

/-- The reciprocal pole coefficient of the section 107 phase remainder. -/
@[expose]
noncomputable def phaseRecip107 : ℝ :=
  (3 * (51 / 50 : ℝ) ^ 5 / (13 / 25) ^ 6) * ((91 / 200 : ℝ) * Real.exp (1 / 10) - (11 / 25))

/-- The combined polynomial multiplying the forward main exponential. -/
@[expose]
noncomputable def phaseMainPoly107 (x : ℝ) : ℝ :=
  -4 * phaseEulerMainPoly107 x +
    ((51 / 50 : ℝ) ^ 5 / 30) *
      ((11 / 25) * x ^ 5 - (91 / 200) * Real.exp ((51 / 50) * (1 / 5)) * (x - 1 / 5) ^ 5)

/-- The section 107 phase remainder in log-cutoff coordinates, with
the powers factored into five exponentials of fixed rates. -/
@[expose]
noncomputable def phaseLog107 (x : ℝ) : ℝ :=
  phasePole107 - 0.000002191 + Real.exp (-(13 / 25) * x) * phaseMainPoly107 x -
        4 * Real.exp (-(51 / 50) * x) * phaseEulerErrorPoly107 x +
      phaseRecip107 * Real.exp (-x / 2) -
    phaseRefCoeff107 *
      (Real.exp (-(77 / 50) * x) * phaseRefMainPoly107 x +
        Real.exp (-(51 / 25) * x) * phaseRefErrorPoly107 x)

/-- The factored polynomial expression agrees with the closed remainder
at every positive radius. -/
theorem phase_closed_log107 {r : ℝ} (hr : 0 < r) :
    phaseClosed107 r = phaseLog107 (2 * Real.log r) := by
  unfold phaseClosed107 phaseLog107 phaseMainPoly107 phaseRecip107 phaseRefCoeff107
  dsimp only
  rw [phase_euler_log107 (sq_pos_of_pos hr), phase_reflected_log107 (sq_pos_of_pos hr),
    Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  rw [show -(2 * Real.log r) / 2 = -Real.log r by ring, Real.exp_neg (Real.log r), Real.exp_log hr]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
