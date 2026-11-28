/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141GammaEndpoints
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141GammaCurvature
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156GammaEndpoints
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156GammaCurvature
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDecayCellUpper
import Mathlib.Tactic.FinCases
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleCells

/-! # Uniform middle Gamma bounds from the checked cells -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Unit-width curvature in a translated rational row is the physical curvature. -/
private theorem translated_curv (P : Polynomial ℚ) (o : ℚ) (r t : ℝ) :
    (gaussianLocalCurv ((P.comp (Polynomial.X + Polynomial.C o)).map (Rat.castHom ℝ)) r 1).eval t =
      (gaussianDecayDeriv r (gaussianDecayDeriv r (P.map (Rat.castHom ℝ)))).eval (t + (o : ℝ)) := by
  simpa only [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    Rat.coe_castHom, Polynomial.C_1, mul_one] using
    gaussian_local_curv_eval (P.map (Rat.castHom ℝ)) r (o : ℝ) 1 t one_ne_zero

/-- The normalized K141 upper Gamma term stays below (23/100) throughout its
physical interval. Both cell curvature bounds enter the interpolation. -/
public theorem middle_k141_gamma_uniform_le {z : ℝ} (hz : z ∈ Set.Icc (47 / 2) (57 / 2)) :
    (middleK141Norm : ℝ) * Real.exp (-2 * z) *
        ((middleGammaUpperPoly middleK141Profile middleK141GammaRow).map (Rat.castHom ℝ)).eval z ≤
      23 / 100 := by
  let P := middleGammaUpperPoly middleK141Profile middleK141GammaRow
  have hκ : 0 ≤ (middleK141Norm : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have hcurv (i : Fin 2) (w : ℝ) (hl : (5 / 2) * (i.val : ℝ) ≤ w - 47 / 2)
    (hr : w - 47 / 2 ≤ middleK141LocalRight i) :
    (middleK141Norm : ℝ) * Real.exp (-2 * w) *
        |(gaussianDecayDeriv 2 (gaussianDecayDeriv 2 (P.map (Rat.castHom ℝ)))).eval w| ≤
      (middleK141GammaCurvCap i : ℝ) / 10 ^ 6 := by
    have h := middle_k141_gamma_curv_le i hl hr
    dsimp only [P] at ⊢
    simp only [translated_curv, Rat.cast_div, Rat.cast_ofNat, sub_add_cancel, add_sub_cancel] at h
    exact h
  have h₀ := middle_k141_gamma_endpoint_le 0
  have h₁ := middle_k141_gamma_endpoint_le 1
  have h₂ := middle_k141_gamma_endpoint_le 2
  change
    (middleK141Norm : ℝ) * Real.exp (-2 * (47 / 2)) * (P.map (Rat.castHom ℝ)).eval (47 / 2) ≤
      12502 / 10 ^ 6 at h₀
  have h₁' :
    (middleK141Norm : ℝ) * Real.exp (-2 * 26) * (P.map (Rat.castHom ℝ)).eval 26 ≤ 69 / 10 ^ 6 := by
    change
      (middleK141Norm : ℝ) * Real.exp (-2 * (52 / 2)) * (P.map (Rat.castHom ℝ)).eval (52 / 2) ≤
        69 / 10 ^ 6 at h₁
    norm_num only at h₁ ⊢
    exact h₁
  change
    (middleK141Norm : ℝ) * Real.exp (-2 * (57 / 2)) * (P.map (Rat.castHom ℝ)).eval (57 / 2) ≤
      6 / 10 ^ 6 at h₂
  by_cases hz' : z ≤ 26
  · have h :=
      gaussian_decay_cell_upper (P.map (Rat.castHom ℝ)) (r := 2) (a := 47 / 2) (b := 26) (M :=
        266046 / 10 ^ 6) (m := 12502 / 10 ^ 6) ⟨hz.1, hz'⟩ hκ (by norm_num only) h₀
        (h₁'.trans (show (69 : ℝ) / 10 ^ 6 ≤ 12502 / 10 ^ 6 by norm_num only))
        (fun w hw ↦ by
          have hc :=
            hcurv 0 w
              (by
                change (5 / 2 : ℝ) * (0 : ℕ) ≤ w - 47 / 2
                norm_num only [Nat.cast_zero, mul_zero]
                linarith only [hw.1])
              (by
                change w - 47 / 2 ≤ 5 / 2; linarith only [hw.2])
          simpa only [middleK141GammaCurvCap, Matrix.cons_val_zero, Nat.cast_ofNat] using hc)
    exact h.trans (by norm_num only)
  · have h :=
      gaussian_decay_cell_upper (P.map (Rat.castHom ℝ)) (r := 2) (a := 26) (b := 57 / 2) (M :=
        6411 / 10 ^ 6) (m := 69 / 10 ^ 6) ⟨(lt_of_not_ge hz').le, hz.2⟩ hκ (by norm_num only) h₁'
        (h₂.trans (by norm_num only))
        (fun w hw ↦ by
          have hc :=
            hcurv 1 w
              (by
                norm_num only [Fin.val_one, Nat.cast_one, mul_one]; linarith only [hw.1])
              (by
                change w - 47 / 2 ≤ 5; linarith only [hw.2])
          simpa only [middleK141GammaCurvCap, Matrix.cons_val_one, Matrix.cons_val_zero,
            Nat.cast_ofNat] using hc)
    exact h.trans (by norm_num only)

/-- The K156 Gamma term after pole subtraction is uniformly bounded by
one thousandth on the closed physical range. -/
public theorem middle_k156_gamma_uniform_le {z : ℝ} (hz : z ∈ Set.Icc (55 / 2) (135 / 4)) :
    (middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * z) *
        (middleK156GammaNet.map (Rat.castHom ℝ)).eval z ≤
      1 / 1000 := by
  have hz' : z - 7 / 2 ∈ Set.Icc (24 : ℝ) (121 / 4) :=
    ⟨by linarith only [hz.1], by linarith only [hz.2]⟩
  obtain ⟨i, hi⟩ := k156_cell_cover hz'
  let a : ℝ := (middleK156EndpointNum i.castSucc : ℝ) / middleK156EndpointDen i.castSucc
  let b : ℝ := (middleK156EndpointNum i.succ : ℝ) / middleK156EndpointDen i.succ
  have hcoords :
    ∀ j : Fin 7,
      (middleK156EndpointNum j.castSucc : ℚ) / middleK156EndpointDen j.castSucc =
          (gaussianK156Cells j).left + 7 / 2 ∧
        (middleK156EndpointNum j.succ : ℚ) / middleK156EndpointDen j.succ =
          (gaussianK156Cells j).right + 7 / 2 ∧
        (gaussianK156Cells j).right - (gaussianK156Cells j).left ≤ 1 := by
    decide +kernel
  have ha : a = ((gaussianK156Cells i).left : ℝ) + 7 / 2 := by
    simpa only [a, Rat.cast_div, Rat.cast_intCast, Rat.cast_add, Rat.cast_ofNat] using
      congrArg (fun q : ℚ ↦ (q : ℝ)) (hcoords i).1
  have hb : b = ((gaussianK156Cells i).right : ℝ) + 7 / 2 := by
    simpa only [b, Rat.cast_div, Rat.cast_intCast, Rat.cast_add, Rat.cast_ofNat] using
      congrArg (fun q : ℚ ↦ (q : ℝ)) (hcoords i).2.1
  have ha' : a = 55 / 2 + (i.val : ℝ) := by
    have h : ∀ j : Fin 7, (gaussianK156Cells j).left = 24 + (j.val : ℚ) := by decide +kernel
    rw [ha, h i, Rat.cast_add, Rat.cast_ofNat, Rat.cast_natCast]
    ring
  have hb' : b = 55 / 2 + middleK156LocalRight i := by
    have h :
      ∀ j : Fin 7,
        (gaussianK156Cells j).right = if j.val = 6 then 121 / 4 else 25 + (j.val : ℚ) := by
      decide +kernel
    rw [hb, h i]
    by_cases hy : i.val = 6
    · norm_num only [middleK156LocalRight, ite_eq_left hy, Rat.cast_div, Rat.cast_ofNat]
    · simp only [middleK156LocalRight, ite_eq_right hy, Rat.cast_add, Rat.cast_ofNat,
        Rat.cast_natCast]
      ring
  have hab : z ∈ Set.Icc a b := ⟨by linarith only [hi.1, ha], by linarith only [hi.2, hb]⟩
  have hend : ∀ j : Fin 8, middleK156EndpointCap j ≤ 486 := by decide +kernel
  have hcap : ∀ j : Fin 7, middleK156GammaCurvCap j ≤ 1058 := by decide +kernel
  have he (j : Fin 8) : (middleK156EndpointCap j : ℝ) / 10 ^ 6 ≤ 486 / 10 ^ 6 :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr (hend j)) (by norm_num only)
  have h :=
    gaussian_decay_cell_upper (middleK156GammaNet.map (Rat.castHom ℝ)) (r := 49 / 20) (m :=
      486 / 10 ^ 6) (M := 1058 / 10 ^ 6) hab (Rat.cast_nonneg.mpr (by decide +kernel))
      (by norm_num only) ((middle_k156_gamma_endpoint_le i.castSucc).trans (he _))
      ((middle_k156_gamma_endpoint_le i.succ).trans (he _))
      (fun w hw ↦ by
        have hc :=
          middle_k156_gamma_curv_le i (t := w - 55 / 2) (by linarith only [ha', hw.1])
            (by linarith only [hb', hw.2])
        simp only [translated_curv, Rat.cast_div, Rat.cast_ofNat, sub_add_cancel,
          add_sub_cancel] at hc
        exact hc.trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr (hcap i)) (by norm_num only)))
  have hw := (Rat.cast_le (K := ℝ)).mpr (hcoords i).2.2
  simp only [Rat.cast_sub, Rat.cast_one] at hw
  have hw₁ : b - a ≤ 1 := by linarith only [hw, ha, hb]
  have hw₀ : 0 ≤ b - a := sub_nonneg.mpr (hab.1.trans hab.2)
  have hsq := pow_le_pow_left₀ hw₀ hw₁ 2
  exact h.trans (by linarith only [hsq])

end PseudoPrime.PrimeTestBounds.MillerRabin
