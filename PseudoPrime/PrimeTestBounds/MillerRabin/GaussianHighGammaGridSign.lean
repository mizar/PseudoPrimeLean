/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaTailBound
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighProfileGrid

/-! # Integer coefficient calculation for the high Gaussian sign certificate -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Compute each upper gamma numerator once, for reuse in the coefficient sums. -/
private def highGammaGridUpperRow (K : HighGaussianKernel) (m N D : ℕ) : Array ℤ :=
  Array.ofFn (fun j : Fin m ↦ (highGammaGrid K N (3 * D) j.val).2)

/-- Compute one translated coefficient from the two integer input rows. -/
private def highGammaGridCoeff (m D : ℕ) (b u : Array ℤ) (i : ℕ) : ℤ :=
  4 * D * b[i]?.getD 0 +
    ∑ j ∈ Finset.range (m - i), u[j]?.getD 0 *
      ((i + j).descFactorial j : ℤ) * b[i + j]?.getD 0

/-- Combine the integer input rows into the translated H34 numerator row. -/
private def highGammaGridCombine (m D : ℕ) (b u : Array ℤ) : Array ℤ :=
  Array.ofFn (fun i : Fin m ↦ highGammaGridCoeff m D b u i.val)

/-- Compute the translated H34 numerator row with gamma denominator `3 * D`
and a shared, exact denominator for the shifted profile. -/
private def highGammaGridNumeratorRow (K : HighGaussianKernel) (N D : ℕ) (a : ℤ) :
    Array ℤ :=
  let m := 2 * K.degree + 4
  highGammaGridCombine m D (highGammaShiftedProfile K a)
    (highGammaGridUpperRow K m N D)

/-- The integer numerator row scales the weighted rational row by
the common denominator of the shifted profile. -/
private theorem high_gamma_grid_numerator_cast (K : HighGaussianKernel) (N D : ℕ)
    (a : ℤ) {i : ℕ} (hi : i < 2 * K.degree + 4) :
    let m := 2 * K.degree + 4
    let B := K.cellPowerRow (a : ℚ) 1
    ((highGammaGridNumeratorRow K N D a)[i]?.getD 0 : ℚ) =
      (highGammaProfileDen m (highGammaBaseRow K) : ℚ) *
        (4 * D * B[i]?.getD 0 +
          ∑ j ∈ Finset.range (m - i),
            ((highGammaGrid K N (3 * D) j).2 : ℚ) *
              ((i + j).descFactorial j : ℚ) * B[i + j]?.getD 0) := by
  intro m B
  dsimp only [m, B]
  simp only [highGammaGridNumeratorRow, highGammaGridCombine, highGammaGridCoeff,
    highGammaGridUpperRow,
    Array.getElem?_ofFn, dite_eq_left hi,
    Option.getD_some, Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_ofNat,
    Int.cast_natCast, high_gamma_shifted_cast K a hi, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hij : i + j < 2 * K.degree + 4 := by
      simpa only [Nat.add_comm] using Nat.lt_sub_iff_add_lt.mp hj'
    have hjm := hj'.trans_le (Nat.sub_le _ _)
    simp only [dite_eq_left hjm, Option.getD_some, high_gamma_shifted_cast K a hij]
    ring

/-- The scaled H34 polynomial in the translated coordinate. -/
private noncomputable def highGammaGridPoly (K : HighGaussianKernel) (N D : ℕ) (a : ℚ) :
    Polynomial ℚ :=
  let Q := K.ratProfile.comp (Polynomial.X + Polynomial.C a)
  Polynomial.C (4 * D : ℚ) * Q +
    ∑ j ∈ Finset.range (2 * K.degree + 4),
      Polynomial.C ((highGammaGrid K N (3 * D) j).2 : ℚ) *
        ((Polynomial.derivative^[j]) Q)

/-- An integer numerator entry gives the corresponding scaled polynomial coefficient. -/
private theorem high_gamma_grid_poly_coeff (K : HighGaussianKernel) (N D : ℕ)
    (a : ℤ) {i : ℕ} (hi : i < 2 * K.degree + 4) :
    ((highGammaGridNumeratorRow K N D a)[i]?.getD 0 : ℚ) =
      (highGammaProfileDen (2 * K.degree + 4) (highGammaBaseRow K) : ℚ) *
        (highGammaGridPoly K N D a).coeff i := by
  let Q := K.ratProfile.comp (Polynomial.X + Polynomial.C (a : ℚ))
  have hd : Q.natDegree ≤ 2 * K.degree + 3 := by
    refine Polynomial.natDegree_comp_le.trans ?_
    simpa only [Polynomial.natDegree_X_add_C, mul_one] using high_rat_profile_degree K
  have hb (k : ℕ) (hk : k < 2 * K.degree + 4) :
      (K.cellPowerRow a 1)[k]?.getD 0 = Q.coeff k := by
    simpa only [Q, Polynomial.C_1, one_mul] using high_cell_power_coeff K a 1 hk
  rw [high_gamma_grid_numerator_cast K N D a hi]
  simp only [highGammaGridPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.finsetSum_coeff, Polynomial.coeff_iterate_derivative, nsmul_eq_mul]
  rw [hb i hi]
  congr 2
  calc
    _ = ∑ j ∈ Finset.range (2 * K.degree + 4 - i),
        ((highGammaGrid K N (3 * D) j).2 : ℚ) *
          (((i + j).descFactorial j : ℚ) * Q.coeff (i + j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hij : i + j < 2 * K.degree + 4 := by
          simpa only [Nat.add_comm] using Nat.lt_sub_iff_add_lt.mp (Finset.mem_range.mp hj)
        rw [hb _ hij, mul_assoc]
    _ = _ := Finset.sum_subset (Finset.range_subset_range.mpr (Nat.sub_le _ _))
      (fun j _ hj ↦ by
        have hij : ¬ i + j < 2 * K.degree + 4 := fun h ↦
          hj (Finset.mem_range.mpr (Nat.lt_sub_iff_add_lt.mpr
            (by simpa only [Nat.add_comm] using h)))
        have hdeg := hd.trans_lt (Nat.lt_of_succ_le (Nat.le_of_not_gt hij))
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, mul_zero, mul_zero])

/-- The shifted numerator polynomial has no terms above the profile degree bound. -/
private theorem high_gamma_grid_poly_degree (K : HighGaussianKernel) (N D : ℕ) (a : ℚ) :
    (highGammaGridPoly K N D a).natDegree ≤ 2 * K.degree + 3 := by
  let Q := K.ratProfile.comp (Polynomial.X + Polynomial.C a)
  have hd : Q.natDegree ≤ 2 * K.degree + 3 := by
    refine Polynomial.natDegree_comp_le.trans ?_
    simpa only [Polynomial.natDegree_X_add_C, mul_one] using high_rat_profile_degree K
  rw [highGammaGridPoly]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans hd
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.natDegree_iterate_derivative _ j).trans ((Nat.sub_le _ _).trans hd))

/-- A passing integer coefficient test bounds the scaled polynomial on the
entire nonnegative half-line in the translated coordinate. -/
private theorem high_gamma_grid_poly_nonpos (K : HighGaussianKernel) (N D : ℕ) (a : ℤ)
    (h : (highGammaGridNumeratorRow K N D a).all (· ≤ 0) = true)
    {t : ℝ} (ht : 0 ≤ t) :
    ((highGammaGridPoly K N D a).map (Rat.castHom ℝ)).eval t ≤ 0 := by
  let P := highGammaGridPoly K N D a
  have hc (i : ℕ) : P.coeff i ≤ 0 := by
    by_cases hi : i < 2 * K.degree + 4
    · have hi' : i < (highGammaGridNumeratorRow K N D a).size := by
        simpa only [highGammaGridNumeratorRow, highGammaGridCombine, Array.size_ofFn] using hi
      have he := high_gamma_grid_poly_coeff K N D a hi
      have h' : (highGammaGridNumeratorRow K N D a)[i]?.getD 0 ≤ 0 := by
        rw [Array.getElem?_eq_getElem hi', Option.getD_some]
        exact of_decide_eq_true (Array.all_eq_true.mp h i hi')
      have hr : (((highGammaGridNumeratorRow K N D a)[i]?.getD 0 : ℤ) : ℚ) ≤ 0 :=
        Int.cast_nonpos.mpr h'
      rw [he] at hr
      exact nonpos_of_mul_nonpos_right hr
        (Nat.cast_pos.mpr (high_gamma_profile_den_pos _ _))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          ((high_gamma_grid_poly_degree K N D a).trans_lt
            (Nat.lt_of_succ_le (Nat.le_of_not_gt hi)))]
  have hs (i : ℕ) : 0 ≤ ((Polynomial.C (1 : ℚ) * -P).comp
      (Polynomial.X + Polynomial.C 0)).coeff i := by
    simpa only [Polynomial.C_1, one_mul, Polynomial.C_0, add_zero, Polynomial.comp_X,
      Polynomial.coeff_neg, neg_nonneg] using hc i
  have hp := profile_shift_nonneg_of_scaled (-P) 0 zero_lt_one hs 0
    (by simpa only [Rat.cast_zero] using ht)
  simpa only [Function.iterate_zero_apply, Polynomial.map_neg, Polynomial.eval_neg,
    neg_nonneg] using hp

/-- The derivative commutes with a unit-width translation. -/
private theorem grid_translate_derivative (P : Polynomial ℚ) (a : ℚ) (j : ℕ) :
    ((Polynomial.derivative^[j]) P).comp (Polynomial.X + Polynomial.C a) =
      (Polynomial.derivative^[j]) (P.comp (Polynomial.X + Polynomial.C a)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Function.iterate_succ_apply', ← ih, Polynomial.derivative_comp,
      Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C, add_zero,
      one_mul]

/-- Evaluating the translated numerator at `z - a` recovers the H34 terms
at `z`, with the integer gamma weights. -/
private theorem high_gamma_grid_poly_eval (K : HighGaussianKernel) (N D : ℕ)
    (a : ℚ) (z : ℝ) :
    ((highGammaGridPoly K N D a).map (Rat.castHom ℝ)).eval (z - a) =
      4 * D * K.realProfile.eval z +
        ∑ j ∈ Finset.range (K.realProfile.natDegree + 1),
          (↑(highGammaGrid K N (3 * D) j).2 : ℝ) *
            ((Polynomial.derivative^[j]) K.realProfile).eval z := by
  have hz : z - (a : ℝ) + (a : ℝ) = z := sub_add_cancel z _
  have hdeg : K.realProfile.natDegree ≤ 2 * K.degree + 3 := by
    rw [← high_comp_profile_map,
      Polynomial.natDegree_map_eq_of_injective (Rat.cast_injective (α := ℝ))]
    exact high_rat_profile_degree K
  simp only [highGammaGridPoly, ← grid_translate_derivative, Polynomial.map_comp,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_sum, ← Polynomial.iterate_derivative_map, high_comp_profile_map,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_comp, Polynomial.eval_finsetSum, Rat.coe_castHom, Rat.cast_mul,
    Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_intCast, hz]
  congr 1
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hdeg))
  intro j _ hj
  have hj' : K.realProfile.natDegree < j :=
    Nat.lt_of_not_ge (fun h ↦ hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
  rw [Polynomial.iterate_derivative_eq_zero hj', Polynomial.eval_zero, mul_zero]

/-- A passing integer test proves the contour offset sign from the translation
point onward, for the same grid upper bounds used by the contour estimate. -/
private theorem high_gamma_grid_offset_nonpos (K : HighGaussianKernel) (N D : ℕ) (a : ℤ)
    (hD : 0 < D) (h : (highGammaGridNumeratorRow K N D a).all (· ≤ 0) = true)
    {z : ℝ} (hz : (a : ℝ) ≤ z) :
    highGammaOffset K (fun j ↦ (↑(highGammaGrid K N (3 * D) j).2 : ℝ) / ↑(3 * D : ℕ)) z ≤ 0 := by
  have hza : ((a : ℚ) : ℝ) ≤ z := by simpa only [Rat.cast_intCast] using hz
  have hn := high_gamma_grid_poly_nonpos K N D a h (sub_nonneg.mpr hza)
  rw [high_gamma_grid_poly_eval] at hn
  let c : ℝ := ↑(3 * D : ℕ)
  have hc : 0 < c := Nat.cast_pos.mpr (Nat.mul_pos (by decide) hD)
  apply nonpos_of_mul_nonpos_right _ hc
  simp only [highGammaOffset, ← show ↑(3 * D : ℕ) = c from rfl, mul_add, Finset.mul_sum]
  have he : c * ((4 / 3 : ℝ) * K.realProfile.eval z) = 4 * D * K.realProfile.eval z := by
    dsimp only [c]
    rw [Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [he]
  refine (le_of_eq (congrArg (fun S ↦ 4 * (D : ℝ) * K.realProfile.eval z + S) ?_)).trans hn
  apply Finset.sum_congr rfl
  intro j _
  change c * ((_ / c) * _) = _
  rw [← mul_assoc, mul_comm c, div_mul_cancel₀ _ hc.ne']

/-- Apply the verified integer H34 test to the zero score of a passing uniform triple. -/
private theorem gaussian_high_score_of_grid
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (K : HighGaussianKernel)
    {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime]
    [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) {X : ℝ} (hX : 1000000 ≤ X)
    (hz : (profileCorrectionEnd K : ℝ) ≤ 5 + Real.log X)
    (N D : ℕ) (hD : 0 < D)
    (hcheck : (highGammaGridNumeratorRow K N D (profileCorrectionEnd K)).all
      (· ≤ 0) = true)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X →
      PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let z := 5 + Real.log X
    let v := fun m : ℕ ↦ 5 - Real.log ((m : ℝ) / X)
    let B := fun m : ℕ ↦ ArithmeticFunction.vonMangoldt m *
      (m : ℝ) ^ (-(1 / 2) : ℝ) * Real.exp (-(K.pole : ℝ) * v m) * K.realProfile.eval (v m)
    4 * (∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, B m) -
        (∑ m ∈ Finset.Ioc 0 ⌊X * Real.exp 5⌋₊, B m) - 4 * highCompensationBound K X ≤
      gaussianPairZeroScore K X hp hq hr +
        (2 * Real.log n - 4) * Real.exp (-(K.pole : ℝ) * z) * K.realProfile.eval z +
        highReflectedBudget K z +
        3 * Real.exp (-z / 2) * (match K with | .k186 => 0 | .k196 => 806) := by
  have h := gaussian_high_zero_score_offset hGRH K hn ho hu hprod hp hq hr hX hz
    (fun j _ ↦ (high_gamma_grid K N (3 * D) j (Nat.mul_pos (by decide) hD)).2)
    (high_gamma_grid_offset_nonpos K N D _ hD hcheck hz) hpass
  cases K <;> exact h

/-- Verify the sign after substituting two independently checked input rows. -/
private theorem high_gamma_grid_check_of_rows (K : HighGaussianKernel) (N D : ℕ) (a : ℤ)
    {b u : Array ℤ}
    (hb : highGammaShiftedProfile K a = b)
    (hu : highGammaGridUpperRow K (2 * K.degree + 4) N D = u)
    (hs : (highGammaGridCombine (2 * K.degree + 4) D b u).all (· ≤ 0) = true) :
    (highGammaGridNumeratorRow K N D a).all (· ≤ 0) = true := by
  simpa only [highGammaGridNumeratorRow, hb, hu] using hs

/-- Multiplying the output by its positive factorial replaces the
descending factorial in each summand by a factor on the input coefficient. -/
private theorem high_gamma_grid_coeff_factorial (m D : ℕ) (b u : Array ℤ) (i : ℕ) :
    (i.factorial : ℤ) * highGammaGridCoeff m D b u i =
      4 * D * ((i.factorial : ℤ) * b[i]?.getD 0) +
        ∑ j ∈ Finset.range (m - i), u[j]?.getD 0 *
          (((i + j).factorial : ℤ) * b[i + j]?.getD 0) := by
  rw [highGammaGridCoeff, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    have h := Nat.factorial_mul_descFactorial (n := i + j) (k := j) (Nat.le_add_left j i)
    rw [Nat.add_sub_cancel] at h
    rw [← h, Nat.cast_mul]
    ring

/-- Apply positive factorial weights to the profile once before convolution. -/
private def highGammaFactorialRow (m : ℕ) (b : Array ℤ) : Array ℤ :=
  Array.ofFn fun i : Fin m ↦ (i.val.factorial : ℤ) * b[i.val]?.getD 0

/-- Check a block using the already weighted profile coefficients. -/
private def highGammaGridBlock (m D : ℕ) (v u : Array ℤ) (start count : ℕ) : Bool :=
  (List.range count).all fun k ↦
    let i := start + k
    decide (4 * D * v[i]?.getD 0 +
      (∑ j ∈ Finset.range (m - i), u[j]?.getD 0 * v[i + j]?.getD 0) ≤ 0)

/-- A passing block proves the original sign of each covered coefficient. -/
private theorem high_gamma_grid_block_sound (m D : ℕ) (b u : Array ℤ) (start count : ℕ)
    (h : highGammaGridBlock m D (highGammaFactorialRow m b) u start count = true)
    {k : ℕ} (hk : k < count) (hi : start + k < m) :
    highGammaGridCoeff m D b u (start + k) ≤ 0 := by
  have hc := of_decide_eq_true (List.all_eq_true.mp h k (List.mem_range.mpr hk))
  have hw (i : ℕ) (hi' : i < m) :
      (highGammaFactorialRow m b)[i]?.getD 0 = (i.factorial : ℤ) * b[i]?.getD 0 := by
    simp only [highGammaFactorialRow, Array.getElem?_ofFn, dite_eq_left hi', Option.getD_some]
  refine nonpos_of_mul_nonpos_right ?_ (show (0 : ℤ) < ((start + k).factorial : ℤ) from
    Int.natCast_pos.mpr (Nat.factorial_pos _))
  rw [high_gamma_grid_coeff_factorial]
  refine (le_of_eq (congrArg₂ (· + ·) ?_ ?_)).trans hc
  · rw [hw _ hi]
  · apply Finset.sum_congr rfl
    intro j hj
    have hij : start + k + j < m := by
      simpa only [Nat.add_comm] using Nat.lt_sub_iff_add_lt.mp (Finset.mem_range.mp hj)
    rw [hw _ hij]

/-- Coefficient signs covering the row certify the assembled test. -/
private theorem high_gamma_grid_check_of_coeff (m D : ℕ) (b u : Array ℤ)
    (h : ∀ i < m, highGammaGridCoeff m D b u i ≤ 0) :
    (highGammaGridCombine m D b u).all (· ≤ 0) = true := by
  apply Array.all_eq_true.mpr
  intro i hi
  have hi' : i < m := by simpa only [highGammaGridCombine, Array.size_ofFn] using hi
  simpa only [highGammaGridCombine, Array.getElem_ofFn] using decide_eq_true (h i hi')

/-- Consecutive blocks of a fixed positive width certify every coefficient.
In the last block, indices outside the row have zero coefficients. -/
private theorem high_gamma_grid_check_of_blocks (m D : ℕ) (b u : Array ℤ) {width : ℕ}
    (hw : 0 < width)
    (h : ∀ k, width * k < m →
      highGammaGridBlock m D (highGammaFactorialRow m b) u (width * k) width = true) :
    (highGammaGridCombine m D b u).all (· ≤ 0) = true := by
  apply high_gamma_grid_check_of_coeff
  intro i hi
  have hs : width * (i / width) < m := (Nat.mul_div_le i width).trans_lt hi
  have he : width * (i / width) + i % width = i := by
    rw [Nat.add_comm, Nat.mod_add_div]
  have hc := high_gamma_grid_block_sound m D b u (width * (i / width)) width
    (h (i / width) hs) (Nat.mod_lt i hw) (by rw [he]; exact hi)
  rw [he] at hc
  exact hc

end PseudoPrime.PrimeTestBounds.MillerRabin
