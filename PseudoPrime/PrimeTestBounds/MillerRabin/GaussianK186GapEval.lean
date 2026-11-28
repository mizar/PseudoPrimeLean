/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapExp
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassRational
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensation
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleReflection
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapMass
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapProfile
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ReflectionCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms

/-! # Directed Horner evaluation of the common K186 rows -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Convert both endpoints from a row denominator to the common fixed-point scale. -/
private def gapRescale (d : ℤ) (I : Analysis.IntegerInterval) : Analysis.IntegerInterval :=
  ⟨(Analysis.roundedConstant k186GapExpScale I.lower d).lower,
    (Analysis.roundedConstant k186GapExpScale I.upper d).upper⟩

/-- Rounding outward preserves the enclosure during the scale change. -/
private theorem gap_rescale_contains {d : ℤ} {I : Analysis.IntegerInterval} {y : ℝ} (hd : 0 < d)
    (h : I.Contains d y) : (gapRescale d I).Contains k186GapExpScale y := by
  have hG : 0 < k186GapExpScale := by decide +kernel
  exact
    ⟨(Analysis.roundedConstant_contains hG hd).1.trans h.1,
      h.2.trans (Analysis.roundedConstant_contains hG hd).2⟩

/-- Evaluate one integer row at a multiple of 1/32 and scale the result. -/
private def gapEval (r : MiddleIntRow) (N : ℕ) (j : ℤ) : Analysis.IntegerInterval :=
  gapRescale r.den (r.evalInterval N j 32)

/-- Interpret a directed Horner enclosure as the corresponding real evaluation. -/
private theorem gap_eval_contains (r : MiddleIntRow) (N : ℕ) (j : ℤ) (hr : 0 < r.den) :
    (gapEval r N j).Contains k186GapExpScale
      (((r.poly N).map (Rat.castHom ℝ)).eval ((j : ℝ) / 32)) := by
  exact gap_rescale_contains hr (r.eval_interval_contains N j 32 hr (by decide))

/-- Evaluate the physical profile at cutoff coordinate `j/32 + 5`. -/
public def k186GapProfileAt (j : ℤ) : Analysis.IntegerInterval :=
  gapEval baseRow 83 (j + 160)

/-- The physical profile evaluation is certified by the existing coefficient row. -/
public theorem k186_gap_profile_at (j : ℤ) :
    (k186GapProfileAt j).Contains k186GapExpScale
      ((HighGaussianKernel.k186.ratProfile.map (Rat.castHom ℝ)).eval ((j : ℝ) / 32 + 5)) := by
  have h := gap_eval_contains baseRow 83 (j + 160) (by decide +kernel)
  rw [base_row_poly, Int.cast_add, Int.cast_ofNat,
    show ((j : ℝ) + 160) / 32 = (j : ℝ) / 32 + 5 by ring] at h
  exact h

/-- Evaluate the combined endpoint polynomial at cutoff coordinate `j/32 + 5`. -/
public def k186GapEndpointAt (j : ℤ) : Analysis.IntegerInterval :=
  gapEval endpointRow 83 (j + 160)

/-- The endpoint evaluation uses the single checked combination of the Laplace rows. -/
public theorem k186_gap_endpoint_at (j : ℤ) :
    let B := HighGaussianKernel.k186.ratProfile
    let P :=
      Polynomial.C 6 *
          (Polynomial.C (13 / 4) * middleMomentPoly B (9 / 4) 0 +
            middleMomentPoly B.derivative (9 / 4) 0) +
        Polynomial.C 3 * middleMomentPoly B (13 / 4) 0
    (k186GapEndpointAt j).Contains k186GapExpScale
      ((P.map (Rat.castHom ℝ)).eval ((j : ℝ) / 32 + 5)) := by
  have h := gap_eval_contains endpointRow 83 (j + 160) (by decide +kernel)
  rw [endpoint_row_poly, Int.cast_add, Int.cast_ofNat,
    show ((j : ℝ) + 160) / 32 = (j : ℝ) / 32 + 5 by ring] at h
  exact h

/-- Evaluate the first Euler moment at a cutoff on the dyadic grid. -/
public def k186GapEulerNineAt (j : ℤ) : Analysis.IntegerInterval :=
  gapEval eulerNineRow 41 j

/-- The cached integer row encloses the first right Euler moment. -/
public theorem k186_gap_euler_nine_at (j : ℤ) :
    (k186GapEulerNineAt j).Contains k186GapExpScale
      (((middleMomentPoly (highGaussianMassPolynomial .k186) (9 / 4) 0).map (Rat.castHom ℝ)).eval
        ((j : ℝ) / 32)) := by
  have h := gap_eval_contains eulerNineRow 41 j (by decide +kernel)
  rw [euler_nine_poly] at h
  exact h

/-- Evaluate the second right Euler moment at a cutoff on the dyadic grid. -/
public def k186GapEulerElevenAt (j : ℤ) : Analysis.IntegerInterval :=
  gapEval eulerElevenRow 43 j

/-- The cached integer row encloses the RH moment of the mass profile. -/
public theorem k186_gap_euler_eleven_at (j : ℤ) :
    let q := highGaussianMassPolynomial .k186
    let Q := Polynomial.X ^ 2 * (Polynomial.C (13 / 4) * q - q.derivative)
    (k186GapEulerElevenAt j).Contains k186GapExpScale
      (((middleMomentPoly Q (11 / 4) 0).map (Rat.castHom ℝ)).eval ((j : ℝ) / 32)) := by
  have h := gap_eval_contains eulerElevenRow 43 j (by decide +kernel)
  rw [euler_eleven_poly] at h
  exact h

/-- Evaluate the undifferentiated right Euler mass at a dyadic cutoff. -/
public def k186GapMassAt (j : ℤ) : Analysis.IntegerInterval :=
  gapEval massRow 41 j

/-- The certified mass row supplies the boundary term of the RH correction. -/
public theorem k186_gap_mass_at (j : ℤ) :
    (k186GapMassAt j).Contains k186GapExpScale
      (((highGaussianMassPolynomial .k186).map (Rat.castHom ℝ)).eval ((j : ℝ) / 32)) := by
  have h := gap_eval_contains massRow 41 j (by decide +kernel)
  rw [mass_row_poly] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
