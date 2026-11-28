/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensation
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassRational
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleReflection
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapMass
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapProfile
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ReflectionCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms

/-! # Common integer second derivative rows for the K186 finite gap -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Apply the squared decay operator at rational rate `a/b`
to an integer row, using only three adjacent coefficients for each output. -/
private def twiceRow (r : MiddleIntRow) (N : ℕ) (a b : ℤ) : MiddleIntRow :=
  ⟨r.den * b ^ 2,
    Array.ofFn fun i : Fin (N + 1) ↦
      a ^ 2 * r.num i.val - 2 * a * b * (i.val + 1 : ℕ) * r.num (i.val + 1) +
        b ^ 2 * (i.val + 1 : ℕ) * (i.val + 2 : ℕ) * r.num (i.val + 2)⟩

/-- The constructed row meets the existing integer derivative check
by construction, independent of the degree, rates and coefficient values. -/
private theorem twice_row_matches (r : MiddleIntRow) (N : ℕ) (a b : ℤ) :
    r.secondMatches N a b (twiceRow r N a b) = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hlt := List.mem_range.mp hi
  apply decide_eq_true
  simp only [twiceRow, MiddleIntRow.num, Array.getElem?_ofFn, dite_eq_left hlt, Option.getD_some]

/-- The integer curvature row represents the twice differentiated
polynomial factor. -/
private theorem twice_row_poly (r : MiddleIntRow) (N : ℕ) (a b : ℤ) (hr : r.den ≠ 0) (hb : b ≠ 0)
    (hs : r.nums.size ≤ N + 1) :
    let d := (a : ℚ) / b
    (twiceRow r N a b).poly N =
      Polynomial.C (d ^ 2) * r.poly N - Polynomial.C (2 * d) * (r.poly N).derivative +
        (r.poly N).derivative.derivative := by
  apply MiddleIntRow.poly_of_secondMatches hb hr (mul_ne_zero hr (pow_ne_zero _ hb)) hs
  · exact (Array.size_ofFn).le
  · exact twice_row_matches r N a b

/-- The full second Euler moment and its mass boundary term share a row. -/
private def eulerLateRow : MiddleIntRow :=
  (((massRow.mulX2 41).add 43 eulerElevenRow).scale 1 6)

/-- The rational Euler boundary polynomial and the RH moment combine exactly. -/
private theorem euler_late_poly :
    let q := highGaussianMassPolynomial .k186
    let Q := Polynomial.X ^ 2 * (Polynomial.C (13 / 4) * q - q.derivative)
    eulerLateRow.poly 43 =
      Polynomial.C (1 / 6) * (Polynomial.X ^ 2 * q + middleMomentPoly Q (11 / 4) 0) := by
  dsimp only
  rw [eulerLateRow, MiddleIntRow.poly_scale,
    MiddleIntRow.poly_add _ _ _ (by decide +kernel) (by decide +kernel), MiddleIntRow.poly_mulX2,
    mass_row_poly, euler_eleven_poly]
  simp only [Int.cast_one, Int.cast_ofNat]

/-- The coefficient of the untranslated physical profile after two decay
derivatives at rate `a/4`. -/
public def k186ProfileCurvNum (a : ℤ) (i : ℕ) : ℤ :=
  (twiceRow baseRow 83 a 4).num i

/-- The denominator is shared by both curvature rates for the physical profile. -/
public def k186ProfileCurvDen : ℤ :=
  (twiceRow baseRow 83 9 4).den

/-- The scalar curvature coefficient agrees with the analytic polynomial. -/
public theorem k186_profile_curv_coeff (a : ℤ) (i : ℕ) :
    let B := HighGaussianKernel.k186.ratProfile
    let d := (a : ℚ) / 4
    (Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative).coeff
        i =
      (k186ProfileCurvNum a i : ℚ) / k186ProfileCurvDen := by
  have h := twice_row_poly baseRow 83 a 4 (by decide +kernel) (by decide) (by decide +kernel)
  simp only [base_row_poly, Int.cast_ofNat] at h
  dsimp only
  rw [← h]
  exact (twiceRow baseRow 83 a 4).poly_coeff_all 83 Array.size_ofFn.le i

/-- The combined endpoint curvature numerator at rate eleven quarters. -/
public def k186EndpointCurvNum (i : ℕ) : ℤ :=
  (twiceRow endpointRow 83 11 4).num i

/-- Denominator of the integer endpoint curvature row. -/
public def k186EndpointCurvDen : ℤ :=
  (twiceRow endpointRow 83 11 4).den

/-- The fixed endpoint curvature coefficient matches the integer row. -/
public theorem k186_endpoint_curv_coeff (i : ℕ) :
    let B := HighGaussianKernel.k186.ratProfile
    let P :=
      Polynomial.C 6 *
          (Polynomial.C (13 / 4) * middleMomentPoly B (9 / 4) 0 +
            middleMomentPoly B.derivative (9 / 4) 0) +
        Polynomial.C 3 * middleMomentPoly B (13 / 4) 0
    (Polynomial.C ((11 / 4 : ℚ) ^ 2) * P - Polynomial.C (2 * (11 / 4 : ℚ)) * P.derivative +
            P.derivative.derivative).coeff
        i =
      (k186EndpointCurvNum i : ℚ) / k186EndpointCurvDen := by
  have h := twice_row_poly endpointRow 83 11 4 (by decide +kernel) (by decide) (by decide +kernel)
  simp only [endpoint_row_poly, Int.cast_ofNat] at h
  dsimp only
  rw [← h]
  exact (twiceRow endpointRow 83 11 4).poly_coeff_all 83 Array.size_ofFn.le i

/-- The first right Euler curvature numerator at rate nine quarters. -/
public def k186EulerNineCurvNum (i : ℕ) : ℤ :=
  (twiceRow eulerNineRow 41 9 4).num i

/-- Denominator of the first right Euler curvature row. -/
public def k186EulerNineCurvDen : ℤ :=
  (twiceRow eulerNineRow 41 9 4).den

/-- The first right Euler curvature coefficient matches the integer row. -/
public theorem k186_euler_nine_curv_coeff (i : ℕ) :
    let P := middleMomentPoly (highGaussianMassPolynomial .k186) (9 / 4) 0
    (Polynomial.C ((9 / 4 : ℚ) ^ 2) * P - Polynomial.C (2 * (9 / 4 : ℚ)) * P.derivative +
            P.derivative.derivative).coeff
        i =
      (k186EulerNineCurvNum i : ℚ) / k186EulerNineCurvDen := by
  have h := twice_row_poly eulerNineRow 41 9 4 (by decide +kernel) (by decide) (by decide +kernel)
  simp only [euler_nine_poly, Int.cast_ofNat] at h
  dsimp only
  rw [← h]
  exact (twiceRow eulerNineRow 41 9 4).poly_coeff_all 41 Array.size_ofFn.le i

/-- The second right Euler curvature numerator after the mass boundary term is included. -/
public def k186EulerElevenCurvNum (i : ℕ) : ℤ :=
  (twiceRow eulerLateRow 43 11 4).num i

/-- Denominator of the second right Euler curvature row. -/
public def k186EulerElevenCurvDen : ℤ :=
  (twiceRow eulerLateRow 43 11 4).den

/-- The second right Euler curvature coefficient matches the integer row. -/
public theorem k186_euler_eleven_curv_coeff (i : ℕ) :
    let q := highGaussianMassPolynomial .k186
    let Q := Polynomial.X ^ 2 * (Polynomial.C (13 / 4) * q - q.derivative)
    let P := Polynomial.C (1 / 6) * (Polynomial.X ^ 2 * q + middleMomentPoly Q (11 / 4) 0)
    (Polynomial.C ((11 / 4 : ℚ) ^ 2) * P - Polynomial.C (2 * (11 / 4 : ℚ)) * P.derivative +
            P.derivative.derivative).coeff
        i =
      (k186EulerElevenCurvNum i : ℚ) / k186EulerElevenCurvDen := by
  have h := twice_row_poly eulerLateRow 43 11 4 (by decide +kernel) (by decide) (by decide +kernel)
  simp only [euler_late_poly, Int.cast_ofNat] at h
  dsimp only
  rw [← h]
  exact (twiceRow eulerLateRow 43 11 4).poly_coeff_all 43 Array.size_ofFn.le i

end PseudoPrime.PrimeTestBounds.MillerRabin
