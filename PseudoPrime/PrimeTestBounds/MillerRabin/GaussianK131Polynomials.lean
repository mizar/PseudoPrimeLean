/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Constants
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Constants
import Mathlib.Data.Fin.VecNotation

/-! # Expanded power-polynomial terms of the K131 comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private noncomputable def shiftPoly (P : Polynomial ℝ) (h : ℝ) : Polynomial ℝ :=
  P.comp (Polynomial.X + Polynomial.C h)

/-- The derivative sum in the K131 exponential moment formula, evaluated
as a polynomial. All source polynomials have degree at most nineteen. -/
noncomputable def k131MomentPoly (P : Polynomial ℝ) (a : ℝ) (m : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range 20,
    Polynomial.C (((j + m).factorial : ℝ) / (j.factorial : ℝ) / a ^ (j + m + 1)) *
      (Polynomial.derivative^[j]) P

private noncomputable def offsets : Fin 4 → ℝ :=
  ![0, 1 / 10, 21 / 10, 9 / 2]

private noncomputable def gram : Fin 4 → ℝ :=
  ![1831 / 10000, -973 / 5000, 1 / 80, -13 / 1250]

/-- The four frequencies in the K131 Gram comparison include the
translation of the main kernel. -/
noncomputable def k131GramFreq (i : Fin 4) : ℝ :=
  9 / 4 + offsets i

/-- The signed coefficients of the four K131 auxiliary frequencies. -/
noncomputable def k131GramCoeff (i : Fin 4) : ℝ :=
  gram i

/-- Each frequency lies between the main translation and seven. -/
theorem k131_gram_freq_mem (i : Fin 4) : k131GramFreq i ∈ Set.Icc (9 / 4 : ℝ) 7 := by
  fin_cases i
  · exact
      ⟨by
        change (9 / 4 : ℝ) ≤ 9 / 4 + 0; norm_num only, by
        change (9 / 4 : ℝ) + 0 ≤ 7; norm_num only⟩
  · exact
      ⟨by
        change (9 / 4 : ℝ) ≤ 9 / 4 + 1 / 10; norm_num only, by
        change (9 / 4 : ℝ) + 1 / 10 ≤ 7; norm_num only⟩
  · exact
      ⟨by
        change (9 / 4 : ℝ) ≤ 9 / 4 + 21 / 10; norm_num only, by
        change (9 / 4 : ℝ) + 21 / 10 ≤ 7; norm_num only⟩
  · exact
      ⟨by
        change (9 / 4 : ℝ) ≤ 9 / 4 + 9 / 2; norm_num only, by
        change (9 / 4 : ℝ) + 9 / 2 ≤ 7; norm_num only⟩

private noncomputable def shiftedFourier (h : ℝ) : Polynomial ℝ :=
  Polynomial.C (1 / 2) *
    (Polynomial.C (Real.exp (-(27 / 16 : ℝ) * |h|)) * shiftPoly gaussianK131Fourier |h| +
      Polynomial.C (Real.exp ((27 / 16 : ℝ) * |h|)) * shiftPoly gaussianK131Fourier (-|h|))

private noncomputable def gramFourier : Polynomial ℝ :=
  (∑ j : Fin 4, Polynomial.C (-gram j) * shiftedFourier (9 / 4 + offsets j)) +
    ∑ i : Fin 4,
      ∑ j : Fin 4, Polynomial.C (gram i * gram j / 2) * shiftedFourier (offsets i - offsets j)

private noncomputable def shiftedInverse : Polynomial ℝ :=
  ∑ j : Fin 4,
    Polynomial.C (-gram j * Real.exp ((27 / 16 : ℝ) * offsets j)) *
      shiftPoly gaussianK131InversePoly (-offsets j)

private noncomputable def k131Prefactor : ℝ :=
  (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))

private noncomputable def gammaMainPoly (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (35 / 16) * P - P.derivative

private noncomputable def mainTailPoly (P : Polynomial ℝ) : Polynomial ℝ :=
  let Q := Polynomial.X ^ 2
  Q * P + k131MomentPoly (Q * gammaMainPoly P) (27 / 16) 0

private noncomputable def remainderGamma : Polynomial ℝ :=
  let B := gaussianK131InversePoly
  let G :=
    Polynomial.C ((19 / 16 : ℝ) ^ 2) * B + Polynomial.C (2 * (19 / 16 : ℝ)) * B.derivative +
      B.derivative.derivative
  Polynomial.C (17 / 10) * k131MomentPoly G (19 / 16) 0 +
    Polynomial.C ((5 / 12) / (2 - 19 / 16 : ℝ)) * G

/-- Expanded polynomial for the radius power minus 19/8, from the
conductor substitution and the two main-tail densities. -/
noncomputable def gaussianK131Poly19 : Polynomial ℝ :=
  Polynomial.C (-2 * k131Prefactor / (519674 / 1000000 : ℝ)) *
        shiftPoly gaussianK131InversePoly (9 / 4) +
      Polynomial.C (-2 * (gaussianK131Amplitude : ℝ) / (519674 / 1000000 : ℝ)) * shiftedInverse -
    Polynomial.C 4 * k131MomentPoly (gaussianK131Fourier + gramFourier) (19 / 16) 0

/-- Expanded polynomial for the radius power minus 27/8. It retains
the shift in the affine radius and the principal Gamma remainder. -/
noncomputable def gaussianK131Poly27 : Polynomial ℝ :=
  let s : ℝ := 519674 / 1000000
  let t : ℝ := 123 / 10
  let h : ℝ := 9 / 4
  let B := gaussianK131InversePoly
  let cR : ℝ := 486361785475175632772883470102367621 / 1000000000000000000000000000000000000
  Polynomial.C (-2 * t * k131Prefactor / s) * shiftPoly B h +
          Polynomial.C (-2 * t * (gaussianK131Amplitude : ℝ) / s) * shiftedInverse -
        Polynomial.C (1 / 6) * (mainTailPoly gaussianK131Fourier + mainTailPoly gramFourier) -
        Polynomial.C (3 * k131Prefactor) * shiftPoly (k131MomentPoly B (19 / 16) 0) h +
      Polynomial.C (cR * k131Prefactor) * shiftPoly B h -
    Polynomial.C (3 * k131Prefactor) * shiftPoly remainderGamma h

private noncomputable def reflectionOffsets : Fin 2 → ℝ :=
  ![1 / 10, 9 / 2]

private noncomputable def reflectionWeights : Fin 2 → ℝ :=
  ![973 / 5000 - 1831 / 10000 * Real.exp (-(27 / 16 : ℝ) * (1 / 10)),
    13 / 1250 - 1 / 80 * Real.exp (-(27 / 16 : ℝ) * (12 / 5))]

private noncomputable def reflectFactor (j : Fin 2) : ℝ :=
  -4 * reflectionWeights j * (gaussianK131Amplitude : ℝ) *
    Real.exp ((27 / 16 : ℝ) * reflectionOffsets j)

private noncomputable def reflectPoly (P : Polynomial ℝ) (j : Fin 2) : Polynomial ℝ :=
  P.comp (Polynomial.C 2 * Polynomial.X - Polynomial.C (reflectionOffsets j))

/-- Expanded polynomial for the radius power minus 23/4, the two lower
reflection moments. -/
noncomputable def gaussianK131Poly23 : Polynomial ℝ :=
  ∑ j : Fin 2,
    Polynomial.C (reflectFactor j) *
      reflectPoly (k131MomentPoly gaussianK131InversePoly (19 / 16) 0) j

/-- Expanded polynomial for the radius power minus 27/4, the higher
reflection moments and their Chebyshev logarithmic factors. -/
noncomputable def gaussianK131PolyHigher : Polynomial ℝ :=
  let B := gaussianK131InversePoly
  let H := gammaMainPoly B
  let M := fun m ↦ k131MomentPoly H (27 / 16) m
  ∑ j : Fin 2,
    Polynomial.C (reflectFactor j / 24) *
      (Polynomial.X ^ 2 * (reflectPoly B j + reflectPoly (M 0) j) +
        Polynomial.C 2 * Polynomial.X * reflectPoly (M 1) j +
        reflectPoly (M 2) j)

private noncomputable def fourierMass (x : ℝ) : ℝ :=
  2 * Real.exp (-(27 / 16 : ℝ) * |x|) * gaussianK131Fourier.eval |x|

private noncomputable def shiftedConductor : ℝ :=
  (∑ j : Fin 4, gram j * fourierMass (9 / 4 + offsets j)) -
    ∑ i : Fin 4, ∑ j : Fin 4, gram i * gram j * fourierMass (offsets i - offsets j) / 2

private noncomputable def positivePole : ℝ :=
  ((gaussianK131Amplitude * kernelNumerator (35 / 16) ^ 2 / (35 / 16 : ℚ) ^ 20 : ℚ) : ℝ)

private noncomputable def halfLineMass : ℝ :=
  ((gaussianK131Amplitude * kernelNumerator (19 / 16) * kernelNumerator (35 / 16) /
        ((27 / 16 : ℚ) ^ 2 - 1 / 4) ^ 10 :
      ℚ) :
    ℝ)

private noncomputable def gramAbsMass : ℝ :=
  ∑ j : Fin 4, |gram j|

private noncomputable def reflectedConstant : ℝ :=
  -6 * halfLineMass * (∑ j : Fin 4, gram j * Real.cosh ((9 / 4 + offsets j) / 2)) +
      3 * halfLineMass *
        (∑ i : Fin 4, ∑ j : Fin 4, gram i * gram j * Real.cosh ((offsets i - offsets j) / 2)) -
    3 * (2 * gramAbsMass + gramAbsMass ^ 2 / 2) * (1 / 100000 : ℝ)

private noncomputable def k131Alpha : ℝ :=
  4 * k131Prefactor * (k131MomentPoly gaussianK131InversePoly (35 / 16) 0).eval (9 / 4) -
    Real.exp (9 / 8) * positivePole -
    3 * positivePole * (∑ j : Fin 4, gram j * Real.exp (-(offsets j) / 2))

private noncomputable def k131Beta : ℝ :=
  3 / 4 - shiftedConductor

/-- Exponents of the eight power-polynomial terms in the K131 comparison. -/
noncomputable def gaussianK131GapExponent : Fin 8 → ℝ :=
  ![-1, 0, 1, 19 / 8, 27 / 8, 5, 23 / 4, 27 / 4]

/-- The eight polynomials of the K131 comparison after the affine
substitution, in the order of the power exponents. -/
noncomputable def gaussianK131GapPoly : Fin 8 → Polynomial ℝ :=
  ![Polynomial.C (k131Alpha - k131Beta / (2 * (519674 / 1000000))),
    Polynomial.C
      (6 * halfLineMass - 3 / 100000 - 25329 / 1000000 + reflectedConstant -
          k131Beta * (123 / 10) / (2 * (519674 / 1000000)) +
        2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16)),
    Polynomial.C gaussianK131Reciprocal, gaussianK131Poly19, gaussianK131Poly27,
    Polynomial.C (-gaussianK131EdgeLoss), gaussianK131Poly23, gaussianK131PolyHigher]

/-- The K131 scalar comparison in the physical radius coordinate. The
principal RH error and the inverse square-root recovery loss remain outside
the eight polynomial terms. -/
@[expose]
noncomputable def gaussianK131Gap (y : ℝ) : ℝ :=
  (∑ j : Fin 8, logPowerPoly (-gaussianK131GapExponent j) (gaussianK131GapPoly j) y) +
    (k131PrincipalError gaussianK131RhCoeff y +
      logPowerPoly (-(1 / 2 : ℝ)) (Polynomial.C (-((81 / 100 : ℝ) * gaussianK131RecoveryVariation)))
        y)

/-- The four outstanding polynomial curvature checks and the two endpoint
checks imply positivity of the fully instantiated K131 comparison. -/
theorem gaussian_k131_gap_pos {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (hsign :
      ∀ y ∈ Set.Ioo (465644807 / 400000 : ℝ) (1036273 / 250),
        logPowerPoly (-(19 / 8 : ℝ)) (logPowerCurvature (19 / 8) gaussianK131Poly19) y ≤ -1 ∧
          logPowerPoly (-(27 / 8 : ℝ)) (logPowerCurvature (27 / 8) gaussianK131Poly27) y ≤ 0 ∧
          logPowerPoly (-(23 / 4 : ℝ)) (logPowerCurvature (23 / 4) gaussianK131Poly23) y ≤ 0 ∧
          logPowerPoly (-(27 / 4 : ℝ)) (logPowerCurvature (27 / 4) gaussianK131PolyHigher) y ≤ 0)
    (hleft : 1 / 200 < gaussianK131Gap (465644807 / 400000))
    (hright : 1 / 200 < gaussianK131Gap (1036273 / 250)) :
    1 / 200 < gaussianK131Gap (gaussianBridgeScale L) := by
  apply
    gaussian_k131_gap_of_polynomials Finset.univ gaussianK131GapExponent gaussianK131GapPoly hL _
      hleft hright
  intro y hy
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hsign y hy
  have hp : 0 < y := (by norm_num only : (0 : ℝ) < 465644807 / 400000).trans hy.1
  have hrec := k131_reciprocal_curvature_le gaussian_k131_reciprocal_le hy.1.le
  have hedge := (gaussian_k131_edge_curvature_lt hp).le
  have hzero₁ (A : ℝ) :
    logPowerPoly (-(-1 : ℝ)) (logPowerCurvature (-1) (Polynomial.C A)) y = 0 := by
    simp only [logPowerPoly, logPowerCurvature, Polynomial.derivative_C, Polynomial.derivative_zero,
      neg_add_cancel, mul_zero, Polynomial.C_0, zero_mul, sub_zero, add_zero, Polynomial.eval_zero]
  have hzero₂ (A : ℝ) : logPowerPoly (-(0 : ℝ)) (logPowerCurvature 0 (Polynomial.C A)) y = 0 := by
    simp only [logPowerPoly, logPowerCurvature, Polynomial.derivative_C, Polynomial.derivative_zero,
      zero_mul, Polynomial.C_0, mul_zero, sub_zero, add_zero, Polynomial.eval_zero]
  simp only [gaussianK131GapExponent, gaussianK131GapPoly, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, hzero₁, hzero₂, zero_add]
  linarith only [h₁, h₂, h₃, h₄, hrec, hedge]

end PseudoPrime.PrimeTestBounds.MillerRabin
