/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapExp
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensation
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassRational
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectCurvatureRat
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAffineHorner
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapCurvRows
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapMass
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapProfile
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ReflectionCert

/-! # Affine normalization of the integer curvature rows -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Enclose one exact integer coefficient at the common high-range scale. -/
private def curvTick (r : MiddleIntRow) (i : ℕ) : Analysis.IntegerInterval :=
  Analysis.roundedConstant k186GapExpScale (r.num i) r.den

/-- Normalize a source row by Horner substitution at the dyadic scale. -/
private def fastAffine (r : MiddleIntRow) (N : ℕ) (a w : ℤ) : MiddleIntRow :=
  ⟨r.den * 32 ^ N, gaussianFastAffineRatio N a w 32 r.num⟩

/-- The optimized row has the same numerator entries and denominator as
the standard affine row. -/
private theorem fast_affine_eq (r : MiddleIntRow) (N : ℕ) (a w : ℤ) :
    fastAffine r N a w = r.affine N a w 32 := by
  simp only [fastAffine, MiddleIntRow.affine, gaussian_fast_ratio_eq]

/-- A normalized coefficient enclosure represents the affine curvature polynomial. -/
private theorem curv_tick_contains (r : MiddleIntRow) (N : ℕ) (a w : ℤ) (hd : 0 < r.den) (i : ℕ) :
    let P :=
      (r.poly N).comp (Polynomial.C ((w : ℚ) / 32) * Polynomial.X + Polynomial.C ((a : ℚ) / 32))
    (P.map (Rat.castHom ℝ)).natDegree ≤ N ∧
      (curvTick (fastAffine r N a w) i).Contains k186GapExpScale
        ((P.map (Rat.castHom ℝ)).coeff i) := by
  intro P
  rw [fast_affine_eq]
  constructor
  · have h : ((r.affine N a w 32).poly N).natDegree ≤ N :=
      Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _)
    rw [r.poly_affine N a w 32 hd.ne' (by decide)] at h
    exact Polynomial.natDegree_map_le.trans h
  · have hden : 0 < (r.affine N a w 32).den := mul_pos hd (pow_pos (by decide) _)
    have h :=
      Analysis.roundedConstant_contains (p := (r.affine N a w 32).num i)
        (by decide +kernel : 0 < k186GapExpScale) hden
    have hs : (r.affine N a w 32).nums.size ≤ N + 1 := by
      simp only [MiddleIntRow.affine, gaussianAffineRatioRow, gaussianAffineIntRow, Array.size_ofFn]
      exact le_rfl
    have hc := (r.affine N a w 32).poly_coeff_all N hs i
    rw [r.poly_affine N a w 32 hd.ne' (by decide)] at hc
    change P.coeff i = _ at hc
    simpa only [curvTick, Polynomial.coeff_map, Rat.coe_castHom, hc, Rat.cast_div,
      Rat.cast_intCast] using h

/-- At the two rates, the same physical source row is normalized at `a/32+5`. -/
private def profileAffine (rate a w : ℤ) : MiddleIntRow :=
  fastAffine (twiceRow baseRow 83 rate 4) 83 (a + 160) w

/-- The fixed endpoint polynomial uses the same physical offset. -/
private def endpointAffine (a w : ℤ) : MiddleIntRow :=
  fastAffine (twiceRow endpointRow 83 11 4) 83 (a + 160) w

/-- The first Euler polynomial is normalized at the logarithmic cutoff itself. -/
private def eulerNineAffine (a w : ℤ) : MiddleIntRow :=
  fastAffine (twiceRow eulerNineRow 41 9 4) 41 a w

/-- The second Euler polynomial uses the logarithmic cutoff and includes the boundary term. -/
private def eulerElevenAffine (a w : ℤ) : MiddleIntRow :=
  fastAffine (twiceRow eulerLateRow 43 11 4) 43 a w

/-- Scalar coefficient lookup for the normalized curvature of the physical profile. -/
public def k186ProfileCurvTick (rate a w : ℤ) (i : ℕ) : Analysis.IntegerInterval :=
  curvTick (profileAffine rate a w) i

/-- The shared profile coefficients can be used without exposing the affine row. -/
public theorem k186_profile_curv_tick (rate a w : ℤ) (i : ℕ) :
    let B := HighGaussianKernel.k186.ratProfile
    let d := (rate : ℚ) / 4
    let Q :=
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative
    let P :=
      Q.comp (Polynomial.C ((w : ℚ) / 32) * Polynomial.X + Polynomial.C (((a + 160 : ℤ) : ℚ) / 32))
    (P.map (Rat.castHom ℝ)).natDegree ≤ 83 ∧
      (k186ProfileCurvTick rate a w i).Contains k186GapExpScale
        ((P.map (Rat.castHom ℝ)).coeff i) := by
  have h :=
    curv_tick_contains (twiceRow baseRow 83 rate 4) 83 (a + 160) w
      (by
        change 0 < (twiceRow baseRow 83 9 4).den; decide +kernel)
      i
  have hpoly := twice_row_poly baseRow 83 rate 4 (by decide +kernel) (by decide) (by decide +kernel)
  simpa only [k186ProfileCurvTick, profileAffine, hpoly, base_row_poly, Int.cast_ofNat] using h

/-- Read one normalized coefficient of the combined forward and reflected term. -/
public def k186EndpointCurvTick (a w : ℤ) (i : ℕ) : Analysis.IntegerInterval :=
  curvTick (endpointAffine a w) i

/-- The endpoint curvature uses the same affine physical shift as the profile. -/
public theorem k186_endpoint_curv_tick (a w : ℤ) (i : ℕ) :
    let B := HighGaussianKernel.k186.ratProfile
    let R :=
      Polynomial.C 6 *
          (Polynomial.C (13 / 4) * middleMomentPoly B (9 / 4) 0 +
            middleMomentPoly B.derivative (9 / 4) 0) +
        Polynomial.C 3 * middleMomentPoly B (13 / 4) 0
    let Q :=
      Polynomial.C ((11 / 4 : ℚ) ^ 2) * R - Polynomial.C (2 * (11 / 4 : ℚ)) * R.derivative +
        R.derivative.derivative
    let P :=
      Q.comp (Polynomial.C ((w : ℚ) / 32) * Polynomial.X + Polynomial.C (((a + 160 : ℤ) : ℚ) / 32))
    (P.map (Rat.castHom ℝ)).natDegree ≤ 83 ∧
      (k186EndpointCurvTick a w i).Contains k186GapExpScale ((P.map (Rat.castHom ℝ)).coeff i) := by
  have h := curv_tick_contains (twiceRow endpointRow 83 11 4) 83 (a + 160) w (by decide +kernel) i
  have hpoly :=
    twice_row_poly endpointRow 83 11 4 (by decide +kernel) (by decide) (by decide +kernel)
  simpa only [k186EndpointCurvTick, endpointAffine, hpoly, endpoint_row_poly, Int.cast_ofNat] using
    h

/-- Read one normalized coefficient of the first right Euler curvature. -/
public def k186EulerNineCurvTick (a w : ℤ) (i : ℕ) : Analysis.IntegerInterval :=
  curvTick (eulerNineAffine a w) i

/-- The first Euler curvature is normalized in the logarithmic coordinate. -/
public theorem k186_euler_nine_curv_tick (a w : ℤ) (i : ℕ) :
    let R := middleMomentPoly (highGaussianMassPolynomial .k186) (9 / 4) 0
    let Q :=
      Polynomial.C ((9 / 4 : ℚ) ^ 2) * R - Polynomial.C (2 * (9 / 4 : ℚ)) * R.derivative +
        R.derivative.derivative
    let P := Q.comp (Polynomial.C ((w : ℚ) / 32) * Polynomial.X + Polynomial.C ((a : ℚ) / 32))
    (P.map (Rat.castHom ℝ)).natDegree ≤ 41 ∧
      (k186EulerNineCurvTick a w i).Contains k186GapExpScale ((P.map (Rat.castHom ℝ)).coeff i) := by
  have h := curv_tick_contains (twiceRow eulerNineRow 41 9 4) 41 a w (by decide +kernel) i
  have hpoly :=
    twice_row_poly eulerNineRow 41 9 4 (by decide +kernel) (by decide) (by decide +kernel)
  simpa only [k186EulerNineCurvTick, eulerNineAffine, hpoly, euler_nine_poly, Int.cast_ofNat] using
    h

/-- Read one normalized coefficient of the second right Euler curvature. -/
public def k186EulerElevenCurvTick (a w : ℤ) (i : ℕ) : Analysis.IntegerInterval :=
  curvTick (eulerElevenAffine a w) i

/-- The second Euler curvature includes its mass term and normalization. -/
public theorem k186_euler_eleven_curv_tick (a w : ℤ) (i : ℕ) :
    let q := highGaussianMassPolynomial .k186
    let M :=
      middleMomentPoly (Polynomial.X ^ 2 * (Polynomial.C (13 / 4) * q - q.derivative)) (11 / 4) 0
    let R := Polynomial.C (1 / 6) * (Polynomial.X ^ 2 * q + M)
    let Q :=
      Polynomial.C ((11 / 4 : ℚ) ^ 2) * R - Polynomial.C (2 * (11 / 4 : ℚ)) * R.derivative +
        R.derivative.derivative
    let P := Q.comp (Polynomial.C ((w : ℚ) / 32) * Polynomial.X + Polynomial.C ((a : ℚ) / 32))
    (P.map (Rat.castHom ℝ)).natDegree ≤ 43 ∧
      (k186EulerElevenCurvTick a w i).Contains k186GapExpScale
        ((P.map (Rat.castHom ℝ)).coeff i) := by
  have h := curv_tick_contains (twiceRow eulerLateRow 43 11 4) 43 a w (by decide +kernel) i
  have hpoly :=
    twice_row_poly eulerLateRow 43 11 4 (by decide +kernel) (by decide) (by decide +kernel)
  simpa only [k186EulerElevenCurvTick, eulerElevenAffine, hpoly, euler_late_poly,
    Int.cast_ofNat] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
