/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141GammaWidth
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaMajorant
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectCurvatureRat
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141GammaWidth
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaWidth

/-! # Cellwise physical curvature bounds for the K141 Gamma term -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Physical curvature bounds in millionths on the two K141 cells. -/
@[expose]
public def middleK141GammaCurvCap (i : Fin 2) : ℕ :=
  ![266046, 6411] i

/-- The right endpoint in the coordinate measured from the first cell. -/
@[expose]
public noncomputable def middleK141LocalRight (i : Fin 2) : ℝ :=
  if i.val = 0 then 5 / 2 else 5

/-- The integer computation uses the exact right endpoint numerator. -/
private def rightNum (_i : Fin 2) : ℤ :=
  5

/-- Only the first cell width is a half-integer. -/
private def rightDen (i : Fin 2) : ℤ :=
  if i.val = 0 then 2 else 1

/-- Unscaled curvature upper bounds obtained from one translated row. -/
private def rawCap (i : Fin 2) : ℤ :=
  ![11771274086904708737282, 42097052567449332749421] i

/-- The absolute integer Horner comparisons certify the two curvature bounds. -/
private theorem curv_check :
    ∀ i : Fin 2,
      upperLocalRow.curvCap 31 2 1 (rightNum i) (rightDen i) ≤ rawCap i * upperLocalRow.den := by
  decide +kernel

/-- The physical right endpoint is represented by the integer ratio. -/
private theorem right_eq (i : Fin 2) : middleK141LocalRight i = (rightNum i : ℝ) / rightDen i := by
  by_cases hi : i.val = 0
  · simp only [middleK141LocalRight, rightNum, rightDen, ite_eq_left hi, Int.cast_ofNat]
  · simp only [middleK141LocalRight, rightNum, rightDen, ite_eq_right hi, Int.cast_ofNat,
      Int.cast_one, div_one]

/-- Transfer the integer cap to the local real polynomial. -/
private theorem raw_curv_le (i : Fin 2) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ middleK141LocalRight i) :
    let Q :=
      (middleGammaUpperPoly middleK141Profile middleK141GammaRow).comp
        (Polynomial.X + Polynomial.C (47 / 2 : ℚ))
    |(gaussianLocalCurv (Q.map (Rat.castHom ℝ)) (2) 1).eval t| ≤ (rawCap i : ℝ) := by
  have hp : ∀ j : Fin 2, 0 ≤ rightNum j := by decide +kernel
  have hd : ∀ j : Fin 2, 0 < rightDen j := by decide +kernel
  have h := upper_curvature_le _ _ (hp i) (hd i) ht₀ (ht₁.trans_eq (right_eq i))
  have hs : (0 : ℝ) < upperLocalRow.den := Int.cast_pos.mpr (by decide +kernel)
  refine (by simpa only [div_one] using h : _ ≤ _).trans ((div_le_iff₀ hs).mpr ?_)
  exact_mod_cast curv_check i

/-- The normalized absolute curvature is bounded on each whole physical cell. -/
public theorem middle_k141_gamma_curv_le (i : Fin 2) {t : ℝ} (hl : (5 / 2) * (i.val : ℝ) ≤ t)
    (hr : t ≤ middleK141LocalRight i) :
    let Q :=
      (middleGammaUpperPoly middleK141Profile middleK141GammaRow).comp
        (Polynomial.X + Polynomial.C (47 / 2 : ℚ))
    (middleK141Norm : ℝ) * Real.exp (-(2 : ℝ) * (47 / 2 + t)) *
        |(gaussianLocalCurv (Q.map (Rat.castHom ℝ)) (2) 1).eval t| ≤
      (middleK141GammaCurvCap i : ℝ) / 10 ^ 6 := by
  intro Q
  have hc :
    ∀ j : Fin 2,
      middleK141Norm * middleGammaExpCap (1880 + 200 * j.val) * (rawCap j : ℚ) ≤
        (middleK141GammaCurvCap j : ℚ) / 10 ^ 6 := by
    decide +kernel
  have hn : ∀ j : Fin 2, 0 ≤ rawCap j := by decide +kernel
  have ht : ((1880 + 200 * i.val : ℕ) : ℝ) / 40 ≤ (2 : ℝ) * (47 / 2 + t) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hl]
  have h :=
    middle_gamma_width_scaled (κ := middleK141Norm) (cap := (rawCap i : ℚ)) (R :=
      (middleK141GammaCurvCap i : ℚ) / 10 ^ 6) (y := (2 : ℝ) * (47 / 2 + t)) (1880 + 200 * i.val)
      (by decide +kernel) (by exact_mod_cast hn i) ht
      (by
        have h₀ : 0 ≤ t := (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)).trans hl
        simpa only [Rat.cast_intCast] using raw_curv_le i h₀ hr)
      (hc i)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast, neg_mul] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
