/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensationPaired
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensationPaired
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensationPartition
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ReflectionCert
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCompIntegerBernstein

/-! # Integer affine and Bernstein evaluation of the K186 compensation -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Integer affine coefficients for the dyadic log cell with start and width
given in the units of the fixed compensation partition. -/
private def k186CompAffine (i w : ℕ) : MiddleIntRow :=
  baseRow.affine 83 (5 * (i : ℤ)) (5 * (w : ℤ)) 524288

/-- The integer affine row represents the normalized K186 profile on its cell. -/
private theorem k186_comp_affine_poly (i w : ℕ) :
    (k186CompAffine i w).poly 83 =
      HighGaussianKernel.k186.ratProfile.comp
        (Polynomial.C (logCoordinate w) * Polynomial.X + Polynomial.C (logCoordinate i)) := by
  have h :=
    baseRow.poly_affine 83 (5 * (i : ℤ)) (5 * (w : ℤ)) 524288 (by decide +kernel) (by decide)
  rw [base_row_poly] at h
  simpa only [k186CompAffine, logCoordinate, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using h

/-- The denominator remains positive for every affine row. -/
private theorem k186_comp_affine_pos (i w : ℕ) : 0 < (k186CompAffine i w).den := by
  change 0 < baseRow.den * (524288 : ℤ) ^ 83
  exact mul_pos (by decide +kernel) (pow_pos (by decide) _)

/-- The compensation evaluator transforms the cell over the integers.
The positive common scale is applied only to the two final moment sums. -/
public def k186CompCellInteger (i w : ℕ) : ℚ × ℚ :=
  let A := k186CompAffine i w
  let den := (A.den : ℚ) * ((83 : ℕ).factorial : ℚ)
  let l := logCoordinate i
  let h := logCoordinate w
  let c := Array.ofFn (fun j : Fin 84 ↦ max 0 (-A.bernsteinNum 83 j.val))
  let clip (j : ℕ) :=
    if hj : j < 84 then c[j]'(Array.size_ofFn.symm ▸ hj) else max 0 (-A.bernsteinNum 83 j)
  let v (j : ℕ) := compIntVariation h⁻¹ (clip j) (Analysis.bernsteinDerivativeCoeff 83 clip j)
  (Analysis.compensationExpUpper ((13 / 4) * l) *
      (compIntMoments 83 2 h (13 / 4) (fun j ↦ clip j.val) / den),
    Analysis.compensationExpUpper ((11 / 4) * l) *
      (compIntMoments 83 1 h (11 / 4) (fun j ↦ v j.val) / ((4 * (h⁻¹).den) * den)))

/-- The integer evaluator returns the same pair of charges as the shared
rational evaluator on each dyadic cell. -/
public theorem k186_comp_cell_integer_eq (i w : ℕ) :
    k186CompCellInteger i w =
      HighGaussianKernel.k186.cellChargeBounds (5 * (i : ℚ) / 524288) (5 * (w : ℚ) / 524288) := by
  let A := k186CompAffine i w
  let den := (A.den : ℚ) * ((83 : ℕ).factorial : ℚ)
  let l := logCoordinate i
  let h := logCoordinate w
  let c (j : ℕ) := max 0 (-A.bernsteinNum 83 j)
  let b (j : ℕ) := max 0 (-cellBernsteinFromPower 83 j (HighGaussianKernel.k186.cellPowerRow l h))
  have hd : 0 ≤ den :=
    mul_nonneg ((Int.cast_pos.mpr (k186_comp_affine_pos i w) : (0 : ℚ) < A.den).le)
      (Nat.cast_nonneg _)
  have hc (j : ℕ) : (c j : ℚ) / den = b j := by
    change ((max 0 (-A.bernsteinNum 83 j) : ℤ) : ℚ) / den = _
    rw [← A.bernstein_clip_eq 83 j (k186_comp_affine_pos i w), k186_comp_affine_poly]
    exact congrArg (fun t : ℚ ↦ max 0 (-t)) (high_cell_bernstein_coeff .k186 l h j)
  simp only [k186CompCellInteger, HighGaussianKernel.cellChargeBounds, HighGaussianKernel.degree,
    Nat.reduceMul, Nat.reduceAdd, HighGaussianKernel.pole,
    show (11 / 4 : ℚ) + 1 / 2 = 13 / 4 by norm_num only,
    show (11 / 4 : ℚ) - 1 / 2 = 9 / 4 by norm_num only, Array.getElem_ofFn, dite_eq_ite, ite_self]
  apply Prod.ext
  · change
      Analysis.compensationExpUpper ((13 / 4) * l) *
          (compIntMoments 83 2 h (13 / 4) (fun j ↦ c j.val) / den) =
        Analysis.compensationExpUpper ((13 / 4) * l) *
          Analysis.compensationMomentSum 83 2 h (13 / 4) (fun j ↦ b j.val)
    rw [comp_int_moments_eq, ← comp_moment_div]
    simp only [hc]
  · change
      Analysis.compensationExpUpper ((11 / 4) * l) *
          (compIntMoments 83 1 h (11 / 4)
              (fun j ↦ compIntVariation h⁻¹ (c j) (Analysis.bernsteinDerivativeCoeff 83 c j)) /
            ((4 * (h⁻¹).den) * den)) =
        Analysis.compensationExpUpper ((11 / 4) * l) *
          Analysis.compensationMomentSum 83 1 h (11 / 4)
            (fun j ↦ |Analysis.bernsteinVariationDirect 83 j.val (9 / 4) h b|)
    rw [comp_int_moments_eq, ← div_div, ← comp_moment_div, ← comp_moment_div]
    simp only [comp_int_variation_eq, ← comp_variation_abs_div _ _ _ _ _ _ hd, hc]

/-- Advance one dyadic cell and accumulate the two upward-rounded charges. -/
private def compIntegerStep (state : ℕ × (ℤ × ℤ)) (w : ℕ) : ℕ × (ℤ × ℤ) :=
  let p := k186CompCellInteger state.1 w
  (state.1 + w, state.2.1 + chargeTicks p.1, state.2.2 + chargeTicks p.2)

/-- If the uncut Bernstein numerators are nonnegative, neither the clipped
row nor its derivative contributes a compensation charge. -/
private theorem k186_comp_cell_zero (i w : ℕ)
    (hs : ∀ j ≤ 83, 0 ≤ (k186CompAffine i w).bernsteinNum 83 j) :
    k186CompCellInteger i w = (0, 0) := by
  let c := fun j : ℕ ↦ max 0 (-(k186CompAffine i w).bernsteinNum 83 j)
  have hc (j : ℕ) (hj : j ≤ 83) : c j = 0 := max_eq_left (neg_nonpos.mpr (hs j hj))
  have hd (j : ℕ) (hj : j ≤ 83) : Analysis.bernsteinDerivativeCoeff 83 c j = 0 := by
    rw [Analysis.bernsteinDerivativeCoeff, hc j hj, hc (j - 1) ((Nat.sub_le j 1).trans hj),
      sub_self, mul_zero, add_zero]
    rcases hj.eq_or_lt with rfl | hj
    · simp only [Nat.sub_self, Nat.cast_zero, zero_mul]
    · rw [hc (j + 1) (Nat.succ_le_of_lt hj), sub_self, mul_zero]
  have hm {m : ℕ} {h s : ℚ} {v : Fin 84 → ℤ} (hz : ∀ j, v j = 0) :
    compIntMoments 83 m h s v = 0 := by
    simp only [compIntMoments, hz, zero_mul, Finset.sum_const_zero, Int.cast_zero, mul_zero]
  simp only [k186CompCellInteger, Array.getElem_ofFn, dite_eq_ite, ite_self]
  change
    (_ * (compIntMoments 83 2 _ _ (fun j ↦ c j) / _),
        _ *
          (compIntMoments 83 1 _ _
              (fun j ↦ compIntVariation _ (c j) (Analysis.bernsteinDerivativeCoeff 83 c j)) /
            _)) =
      (0, 0)
  rw [hm (fun j ↦ hc j (Nat.le_of_lt_succ j.isLt)), hm (fun j ↦ ?_)]
  · simp only [zero_div, mul_zero]
  · rw [hc j (Nat.le_of_lt_succ j.isLt), hd j (Nat.le_of_lt_succ j.isLt)]
    simp only [compIntVariation, mul_zero, sub_self, abs_zero]

/-- A sign certificate lets the verifier advance across a cell without
recomputing either moment or either exponential bound. -/
private theorem comp_integer_step_zero (i w : ℕ) (a : ℤ × ℤ)
    (hs : ∀ j ≤ 83, 0 ≤ (k186CompAffine i w).bernsteinNum 83 j) :
    compIntegerStep (i, a) w = (i + w, a) := by
  rw [compIntegerStep, k186_comp_cell_zero i w hs]
  simp only [chargeTicks, mul_zero, Int.ceil_zero, add_zero, Prod.eta]

/-- Test whether the uncut Bernstein row is nonnegative on a dyadic cell. -/
private def k186CompSign (i w : ℕ) : Bool :=
  let row := k186CompAffine i w
  (List.range 84).all (fun j ↦ decide (0 ≤ row.bernsteinNum 83 j))

/-- The sign check certifies an exact zero increment for either accumulator. -/
private theorem comp_step_of_sign (i w : ℕ) (a : ℤ × ℤ) (hs : k186CompSign i w = true) :
    compIntegerStep (i, a) w = (i + w, a) := by
  apply comp_integer_step_zero
  intro j hj
  exact of_decide_eq_true (List.all_eq_true.mp hs j (List.mem_range.mpr (Nat.lt_succ_of_le hj)))

/-- The integer traversal preserves both rounded totals for every initial state. -/
private theorem comp_integer_fold_eq (ws : List ℕ) (i : ℕ) (a : ℤ × ℤ) :
    (ws.foldl compIntegerStep (i, a)).2 = accumulateChargePairs .k186 ws i a := by
  induction ws generalizing i a with
  | nil => rfl
  | cons w ws
    ih =>
    let p := HighGaussianKernel.k186.cellChargeBounds (logCoordinate i) (logCoordinate w)
    change
      (ws.foldl compIntegerStep
            (i + w, a.1 + chargeTicks (k186CompCellInteger i w).1,
              a.2 + chargeTicks (k186CompCellInteger i w).2)).2 =
        accumulateChargePairs .k186 ws (i + w) (a.1 + chargeTicks p.1, a.2 + chargeTicks p.2)
    rw [k186_comp_cell_integer_eq]
    exact ih (i + w) _

/-- Executable integer-affine evaluation of the full fixed K186 partition.
The pair contains the main and variation ticks in their original order. -/
public def k186CompIntegerTicks : ℤ × ℤ :=
  ((cellWidths .k186).foldl compIntegerStep (0, 0, 0)).2

/-- The integer evaluation computes the same ticks used by the analytic
K186 compensation bound. -/
public theorem k186_comp_integer_ticks_eq :
    k186CompIntegerTicks = highCompensationChargeTicks .k186 := by
  exact
    (comp_integer_fold_eq (cellWidths .k186) 0 (0, 0)).trans
      (high_compensation_paired_ticks_eq .k186)

end PseudoPrime.PrimeTestBounds.MillerRabin
