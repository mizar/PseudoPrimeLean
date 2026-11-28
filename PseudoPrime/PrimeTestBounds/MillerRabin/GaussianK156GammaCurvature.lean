/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156GammaNet
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectCurvatureRat
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156GammaNet
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaWidth

/-! # Cellwise physical curvature bounds for the K156 Gamma term -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Physical curvature bounds in millionths on the seven consecutive K156 cells. -/
@[expose]
public def middleK156GammaCurvCap (i : Fin 7) : ℕ :=
  ![1058, 597, 336, 188, 106, 59, 9] i

/-- The right endpoint in the coordinate measured from the first cell. -/
@[expose]
public noncomputable def middleK156LocalRight (i : Fin 7) : ℝ :=
  if i.val = 6 then 25 / 4 else (i.val : ℝ) + 1

/-- The integer computation uses the exact right endpoint numerator. -/
private def rightNum (i : Fin 7) : ℤ :=
  if i.val = 6 then 25 else (i.val : ℤ) + 1

/-- The first six local right endpoints are integers. -/
private def rightDen (i : Fin 7) : ℤ :=
  if i.val = 6 then 4 else 1

/-- Unscaled curvature upper bounds obtained from one translated row. -/
private def rawCap (i : Fin 7) : ℤ :=
  ![29025986613237205402934068265, 189726483725080363168853672167, 1235938826398710676687288102051,
      8026392839187023385851506439345, 52091375227941442017218122233910,
      337539621859371167313740590803372, 538015893612216040736123834336850]
    i

/-- The absolute integer Horner comparisons certify the seven curvature bounds. -/
private theorem curv_check :
    ∀ i : Fin 7,
      netLocalRow.curvCap 80 49 20 (rightNum i) (rightDen i) ≤ rawCap i * netLocalRow.den := by
  decide +kernel

/-- The physical right endpoint is represented by the integer ratio. -/
private theorem right_eq (i : Fin 7) : middleK156LocalRight i = (rightNum i : ℝ) / rightDen i := by
  by_cases hi : i.val = 6
  · simp only [middleK156LocalRight, rightNum, rightDen, ite_eq_left hi, Int.cast_ofNat]
  · simp only [middleK156LocalRight, rightNum, rightDen, ite_eq_right hi, Int.cast_add,
      Int.cast_natCast, Int.cast_one, div_one]

/-- Transfer the integer cap to the local real polynomial. -/
private theorem raw_curv_le (i : Fin 7) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ middleK156LocalRight i) :
    let Q := middleK156GammaNet.comp (Polynomial.X + Polynomial.C (55 / 2 : ℚ))
    |(gaussianLocalCurv (Q.map (Rat.castHom ℝ)) (49 / 20) 1).eval t| ≤ (rawCap i : ℝ) := by
  have hp : ∀ j : Fin 7, 0 ≤ rightNum j := by decide +kernel
  have hd : ∀ j : Fin 7, 0 < rightDen j := by decide +kernel
  have h := net_curvature_le _ _ (hp i) (hd i) ht₀ (ht₁.trans_eq (right_eq i))
  have hs : (0 : ℝ) < netLocalRow.den := Int.cast_pos.mpr (by decide +kernel)
  refine h.trans ((div_le_iff₀ hs).mpr ?_)
  exact_mod_cast curv_check i

/-- The normalized absolute curvature is bounded on each whole physical cell. -/
public theorem middle_k156_gamma_curv_le (i : Fin 7) {t : ℝ} (hl : (i.val : ℝ) ≤ t)
    (hr : t ≤ middleK156LocalRight i) :
    let Q := middleK156GammaNet.comp (Polynomial.X + Polynomial.C (55 / 2 : ℚ))
    (middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * (55 / 2 + t)) *
        |(gaussianLocalCurv (Q.map (Rat.castHom ℝ)) (49 / 20) 1).eval t| ≤
      (middleK156GammaCurvCap i : ℝ) / 10 ^ 6 := by
  intro Q
  have hc :
    ∀ j : Fin 7,
      middleK156Norm * middleGammaExpCap (2695 + 98 * j.val) * (rawCap j : ℚ) ≤
        (middleK156GammaCurvCap j : ℚ) / 10 ^ 6 := by
    decide +kernel
  have hn : ∀ j : Fin 7, 0 ≤ rawCap j := by decide +kernel
  have ht : ((2695 + 98 * i.val : ℕ) : ℝ) / 40 ≤ (49 / 20 : ℝ) * (55 / 2 + t) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hl]
  have h :=
    middle_gamma_width_scaled (κ := middleK156Norm) (cap := (rawCap i : ℚ)) (R :=
      (middleK156GammaCurvCap i : ℚ) / 10 ^ 6) (y := (49 / 20 : ℝ) * (55 / 2 + t))
      (2695 + 98 * i.val) (by decide +kernel) (by exact_mod_cast hn i) ht
      (by simpa only [Rat.cast_intCast] using raw_curv_le i ((Nat.cast_nonneg _).trans hl) hr)
      (hc i)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast, neg_mul] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
