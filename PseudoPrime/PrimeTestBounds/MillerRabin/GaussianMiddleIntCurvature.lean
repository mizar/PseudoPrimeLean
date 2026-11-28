/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms

/-! # Curvature bounds from shared integer coefficient rows -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Compute an absolute curvature cap on `[0, p / d]` at the row's scale.
The rate is `rn / rd` and the local coordinate has unit width. -/
@[expose]
public def MiddleIntRow.curvCap (r : MiddleIntRow) (N : ℕ) (rn rd p d : ℤ) : ℤ :=
  let row :=
    Array.ofFn fun i : Fin (N + 1) ↦ (⟨r.num i.val, r.num i.val⟩ : Analysis.IntegerInterval)
  gaussianAbsHorner p d (List.ofFn fun i : Fin (N + 1) ↦ gaussianCurvRowTick rn rd 1 1 row i.val)

/-- The integer cap bounds the local exponential-polynomial curvature
throughout the real interval given by the rational right endpoint. -/
public theorem MiddleIntRow.curv_cap_le (r : MiddleIntRow) (N : ℕ) (rn rd p d : ℤ) (hr : 0 < r.den)
    (hrd : 0 < rd) (hp : 0 ≤ p) (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ (p : ℝ) / d) :
    |(gaussianLocalCurv ((r.poly N).map (Rat.castHom ℝ)) ((rn : ℝ) / rd) 1).eval t| ≤
      (r.curvCap N rn rd p d : ℝ) / r.den := by
  have hQ : ((r.poly N).map (Rat.castHom ℝ)).natDegree < N + 1 := by
    rw [Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℝ).injective]
    exact Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _
  let row :=
    Array.ofFn fun i : Fin (N + 1) ↦ (⟨r.num i.val, r.num i.val⟩ : Analysis.IntegerInterval)
  have hc :
    ∀ i : ℕ, (row[i]?.getD ⟨0, 0⟩).Contains r.den (((r.poly N).map (Rat.castHom ℝ)).coeff i) := by
    intro i
    rw [Polynomial.coeff_map, Rat.coe_castHom]
    by_cases hi : i < N + 1
    · simp only [row, Array.getElem?_ofFn, dite_eq_left hi, Option.getD_some,
        r.poly_coeff (Nat.le_of_lt_succ hi), Rat.cast_div, Rat.cast_intCast,
        Analysis.IntegerInterval.Contains, le_refl, and_self]
    · simp only [row, Array.getElem?_ofFn, dite_eq_right hi, Option.getD_none, poly,
        Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi), Rat.cast_zero,
        Analysis.IntegerInterval.Contains, Int.cast_zero, zero_div, le_refl, and_self]
  have h :=
    gaussian_curv_row_eval_le (rn := rn) (N := N + 1) hr hrd Int.zero_lt_one Int.zero_lt_one hp hd
      ht ht' row _ ((gaussian_local_curv_degree _ _ _).trans_lt hQ) hc
  simpa only [Int.cast_one, div_one, curvCap, row] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
