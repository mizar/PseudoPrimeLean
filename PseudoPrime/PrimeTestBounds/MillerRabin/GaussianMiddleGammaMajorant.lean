/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms

/-! # Physical upper bounds for the middle Gamma derivative sums -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Replace the signed Gamma coefficients by the checked upper row and
add the certified physical width allowance for the centered cell. -/
public theorem middle_gamma_scaled_width_le (P : Polynomial ℚ) (b : ℕ → ℚ × ℚ) (g : ℕ → ℝ) {c h : ℚ}
    {z W ε : ℝ} (hz : |z - (c : ℝ)| ≤ (h : ℝ)) (hW : 0 ≤ W)
    (hb : ∀ j ≤ P.natDegree, ((b j).1 : ℝ) ≤ g j ∧ g j ≤ ((b j).2 : ℝ))
    (hcap : W * (middleGammaWidthBudget P c h b : ℝ) ≤ ε) :
    let R := P.map (Rat.castHom ℝ)
    let v := fun j : ℕ ↦ ((Polynomial.derivative^[j]) R).eval z
    W * (∑ j ∈ Finset.range (P.natDegree + 1), g j * v j) ≤
      W * (∑ j ∈ Finset.range (P.natDegree + 1), ((b j).2 : ℝ) * v j) + ε := by
  intro R v
  have h := mul_le_mul_of_nonneg_left (middle_gamma_width_le P b g hz hb) hW
  rw [mul_add] at h
  exact h.trans (add_le_add_right hcap _)

/-- Form the rational polynomial for the upper coefficient row once.
Its real evaluation is the derivative sum used in every cell. -/
public noncomputable def middleGammaUpperPoly (P : Polynomial ℚ) (b : ℕ → ℚ × ℚ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (P.natDegree + 1), Polynomial.C (b j).2 * (Polynomial.derivative^[j]) P

/-- The contribution to one upper coefficient is a sum of weighted falling factorials.
This formula lets the numeric checker form the coefficient row without building any
intermediate derivative polynomial. -/
public theorem middle_gamma_upper_poly_coeff (P : Polynomial ℚ) (b : ℕ → ℚ × ℚ) (k : ℕ) :
    (middleGammaUpperPoly P b).coeff k =
      ∑ j ∈ Finset.range (P.natDegree + 1),
        (b j).2 * (((k + j).descFactorial j : ℕ) : ℚ) * P.coeff (k + j) := by
  simp only [middleGammaUpperPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_iterate_derivative, nsmul_eq_mul, mul_assoc]

/-- Compute a numerator of the upper polynomial from two common-denominator rows.
Terms with source index above the degree bound are omitted. -/
@[expose]
public def middleGammaIntCoeff (N : ℕ) (p w : ℕ → ℤ) (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (N + 1 - k), w j * ((k + j).descFactorial j : ℤ) * p (k + j)

/-- The integer convolution gives the upper coefficient over the product of the
profile and weight denominators. The caller supplies the row identities. -/
public theorem middle_gamma_int_coeff_eq (P : Polynomial ℚ) (b : ℕ → ℚ × ℚ) (N k : ℕ)
    (hP : P.natDegree ≤ N) (p w : ℕ → ℤ) (D E : ℤ) (hp : ∀ i, P.coeff i = (p i : ℚ) / D)
    (hw : ∀ j < N + 1, (b j).2 = (w j : ℚ) / E) :
    (middleGammaUpperPoly P b).coeff k = (middleGammaIntCoeff N p w k : ℚ) / (D * E) := by
  rw [middle_gamma_upper_poly_coeff]
  let f := fun j : ℕ ↦ (b j).2 * ((k + j).descFactorial j : ℚ) * P.coeff (k + j)
  change (∑ j ∈ Finset.range (P.natDegree + 1), f j) = _
  rw [Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hP))]
  · rw [← Finset.sum_subset (Finset.range_subset_range.mpr (Nat.sub_le (N + 1) k))]
    · simp only [middleGammaIntCoeff, Int.cast_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [f]
      rw [hp, hw j ((Finset.mem_range.mp hj).trans_le (Nat.sub_le (N + 1) k))]
      simp only [Int.cast_mul, Int.cast_natCast, div_eq_mul_inv, mul_inv_rev]
      ac_rfl
    · intro j _ hj
      have hj' := Nat.le_of_not_gt (fun h ↦ hj (Finset.mem_range.mpr h))
      have hz : N < k + j :=
        Nat.lt_of_succ_le ((Nat.sub_le_iff_le_add.mp hj').trans_eq (Nat.add_comm j k))
      simp only [f, Polynomial.coeff_eq_zero_of_natDegree_lt (hP.trans_lt hz), mul_zero]
  · intro j _ hj
    have hj' := Nat.le_of_not_gt (fun h ↦ hj (Finset.mem_range.mpr h))
    have hz : P.natDegree < k + j := (Nat.lt_of_succ_le hj').trans_le (Nat.le_add_left j k)
    simp only [f, Polynomial.coeff_eq_zero_of_natDegree_lt hz, mul_zero]

/-- Construct the shared upper row with one integer convolution per output coefficient. -/
@[expose]
public def MiddleIntRow.gammaUpper (r w : MiddleIntRow) (N : ℕ) : MiddleIntRow :=
  ⟨r.den * w.den, Array.ofFn fun k : Fin (N + 1) ↦ middleGammaIntCoeff N r.num w.num k.val⟩

/-- A weight row agreeing with the upper endpoints yields an integer representation
of the entire upper polynomial, suitable for subsequent translation and evaluation. -/
public theorem MiddleIntRow.gamma_upper_poly (r w : MiddleIntRow) (N : ℕ) (b : ℕ → ℚ × ℚ)
    (hs : r.nums.size ≤ N + 1) (hw : ∀ j < N + 1, (b j).2 = (w.num j : ℚ) / w.den) :
    (r.gammaUpper w N).poly N = middleGammaUpperPoly (r.poly N) b := by
  have hP : (r.poly N).natDegree ≤ N :=
    Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _)
  ext k
  rw [(r.gammaUpper w N).poly_coeff_all N (by simp only [gammaUpper, Array.size_ofFn, le_refl]) k,
    middle_gamma_int_coeff_eq _ _ N k hP r.num w.num r.den w.den (r.poly_coeff_all N hs) hw]
  by_cases hk : k < N + 1
  · simp only [gammaUpper, num, Array.getElem?_ofFn, dite_eq_left hk, Option.getD_some,
      Int.cast_mul]
  · have hz : N + 1 - k = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hk)
    simp only [gammaUpper, num, Array.getElem?_ofFn, dite_eq_right hk, Option.getD_none,
      middleGammaIntCoeff, hz, Finset.range_zero, Finset.sum_empty, Int.cast_zero, zero_div]

/-- Clear the denominators of the upper weight endpoints using the supplied scale. -/
@[expose]
public def middleGammaWeightRow (N D : ℕ) (b : ℕ → ℚ × ℚ) : MiddleIntRow :=
  ⟨D,
    Array.ofFn fun j : Fin (N + 1) ↦
      let q := (b j.val).2
      q.num * (D / q.den : ℕ)⟩

/-- A nonzero scale divisible by each input denominator gives the exact upper weights. -/
public theorem middle_gamma_weight_row_eq (N D : ℕ) (b : ℕ → ℚ × ℚ) (hD : D ≠ 0) (j : ℕ)
    (hj : j < N + 1) (hd : (b j).2.den ∣ D) :
    (b j).2 = ((middleGammaWeightRow N D b).num j : ℚ) / (middleGammaWeightRow N D b).den := by
  simp only [middleGammaWeightRow, MiddleIntRow.num, Array.getElem?_ofFn, dite_eq_left hj,
    Option.getD_some, Int.cast_mul, Int.cast_natCast]
  have hmul : ((D / (b j).2.den : ℕ) : ℚ) * ((b j).2.den : ℚ) = (D : ℚ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hd]
  apply (eq_div_iff (Nat.cast_ne_zero.mpr hD)).mpr
  calc
    _ = (((b j).2.num : ℚ) / (b j).2.den) * (D : ℚ) :=
      congrArg (fun q : ℚ ↦ q * (D : ℚ)) (Rat.num_div_den (b j).2).symm
    _ = _ := by
      rw [← hmul, mul_comm _ ((b j).2.den : ℚ), ← mul_assoc,
        div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (b j).2.den_ne_zero)]

/-- Evaluating the upper polynomial reproduces the real derivative sum. -/
public theorem middle_gamma_upper_poly_eval (P : Polynomial ℚ) (b : ℕ → ℚ × ℚ) (z : ℝ) :
    ((middleGammaUpperPoly P b).map (Rat.castHom ℝ)).eval z =
      ∑ j ∈ Finset.range (P.natDegree + 1),
        ((b j).2 : ℝ) * ((Polynomial.derivative^[j]) (P.map (Rat.castHom ℝ))).eval z := by
  have hm (j : ℕ) :
    (((Polynomial.derivative^[j]) P).map (Rat.castHom ℝ)) =
      (Polynomial.derivative^[j]) (P.map (Rat.castHom ℝ)) := by
    induction j with
    | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply]
    | succ j ih =>
      rw [Function.iterate_succ_apply', ← Polynomial.derivative_map, ih,
        Function.iterate_succ_apply']
  simp only [middleGammaUpperPoly, Polynomial.map_sum, Polynomial.eval_finsetSum,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C, Rat.coe_castHom,
    hm]

/-- With the physical width budget certified, the complete derivative
sum is bounded by one upper polynomial evaluation and the allowance. -/
public theorem middle_gamma_scaled_poly_le (P : Polynomial ℚ) (b : ℕ → ℚ × ℚ) (g : ℕ → ℝ) {c h : ℚ}
    {z W ε : ℝ} (hz : |z - (c : ℝ)| ≤ (h : ℝ)) (hW : 0 ≤ W)
    (hb : ∀ j ≤ P.natDegree, ((b j).1 : ℝ) ≤ g j ∧ g j ≤ ((b j).2 : ℝ))
    (hcap : W * (middleGammaWidthBudget P c h b : ℝ) ≤ ε) :
    W *
        (∑ j ∈ Finset.range (P.natDegree + 1),
          g j * ((Polynomial.derivative^[j]) (P.map (Rat.castHom ℝ))).eval z) ≤
      W * ((middleGammaUpperPoly P b).map (Rat.castHom ℝ)).eval z + ε := by
  rw [middle_gamma_upper_poly_eval]
  exact middle_gamma_scaled_width_le P b g hz hW hb hcap

end PseudoPrime.PrimeTestBounds.MillerRabin
