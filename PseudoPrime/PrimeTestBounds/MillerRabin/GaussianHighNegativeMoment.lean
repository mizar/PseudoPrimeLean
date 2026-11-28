/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighProfileSign
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceSignCell
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
import Mathlib.Algebra.GCDMonoid.Finset

/-! # Finite negative moments for the high Gaussian profiles -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Number of quarter-width cells in the H28 correction interval. -/
private def correctionCellCount : HighGaussianKernel → ℕ
  | .k186 => 120
  | .k196 => 150

/-- The rational left endpoint of a quarter-width H28 cell. -/
private def correctionNode (K : HighGaussianKernel) (i : ℕ) : ℚ :=
  profileCorrectionStart K + (i : ℚ) / 4

/-- The integer coordinate for a quarter-width cell endpoint. -/
private def correctionTick (K : HighGaussianKernel) (i : ℕ) : ℕ :=
  (match K with
    | .k186 => 140
    | .k196 => 170) +
    i

/-- Scaling back the integer coordinate recovers the rational endpoint. -/
private theorem correction_tick_eq (K : HighGaussianKernel) (i : ℕ) :
    (correctionTick K i : ℚ) / 4 = correctionNode K i := by
  cases K <;>
    simp only [correctionTick, correctionNode, profileCorrectionStart, Nat.cast_add,
      Nat.cast_ofNat] <;>
    ring

/-- The rational Bernstein charge on a contiguous block. -/
private noncomputable def negativeBlockCharge (K : HighGaussianKernel) (j start count : ℕ) : ℚ :=
  let P := (Polynomial.derivative^[j]) K.ratProfile
  let n := 2 * K.degree + 3 - j
  let p := fun i ↦ correctionNode K (start + i)
  let s := K.pole - 1 / 2
  ∑ i ∈ Finset.range count,
    Analysis.compensationExpUpper (s * p i) *
      ((p (i + 1) - p i) *
        ((∑ k : Fin (n + 1),
            max 0
              (-Analysis.bernsteinRatCoeff
                  (P.comp (Polynomial.C (p (i + 1) - p i) * Polynomial.X + Polynomial.C (p i))) n
                  k)) /
          ((n : ℚ) + 1)))

/-- The clipped Bernstein charge of the full finite correction interval. -/
public noncomputable def highNegativeMomentCharge (K : HighGaussianKernel) (j : ℕ) : ℚ :=
  negativeBlockCharge K j 0 (correctionCellCount K)

/-- The actual H28 negative moment, independent of the certificate
partition used to bound it. -/
@[expose]
public noncomputable def highNegativeMoment (K : HighGaussianKernel) (j : ℕ) : ℝ :=
  let P := (Polynomial.derivative^[j]) K.realProfile
  let s := (K.pole : ℝ) - 1 / 2
  ∫ t in (profileCorrectionStart K : ℝ)..(profileCorrectionEnd K : ℝ),
    Real.exp (-s * t) * max 0 (-P.eval t)

/-- Differentiation through a quarter-width affine substitution multiplies
the derivative of the substituted polynomial by four at each step. -/
private theorem derivative_quarter_comp (P : Polynomial ℚ) (l : ℚ) (j : ℕ) :
    ((Polynomial.derivative^[j]) P).comp (Polynomial.C (1 / 4) * Polynomial.X + Polynomial.C l) =
      Polynomial.C (4 ^ j) *
        (Polynomial.derivative^[j])
          (P.comp (Polynomial.C (1 / 4) * Polynomial.X + Polynomial.C l)) := by
  let Q : Polynomial ℚ := Polynomial.C (1 / 4) * Polynomial.X + Polynomial.C l
  change
    ((Polynomial.derivative^[j]) P).comp Q =
      Polynomial.C (4 ^ j) * (Polynomial.derivative^[j]) (P.comp Q)
  have hQ : Q.derivative = Polynomial.C (1 / 4) := by
    simp only [Q, Polynomial.derivative_add, Polynomial.derivative_C_mul, Polynomial.derivative_X,
      Polynomial.derivative_C, add_zero, mul_one]
  induction j with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, Polynomial.C_1, one_mul]
  | succ j ih =>
    have hd := congrArg Polynomial.derivative ih
    rw [Polynomial.derivative_comp, hQ, Polynomial.derivative_C_mul] at hd
    simp only [Function.iterate_succ_apply', pow_succ]
    calc
      _ =
          Polynomial.C 4 *
            (Polynomial.C (1 / 4 : ℚ) *
              (Polynomial.derivative ((Polynomial.derivative^[j]) P)).comp Q) :=
        by
        rw [← mul_assoc, ← Polynomial.C_mul]
        norm_num only [mul_div_assoc, mul_one, div_self, OfNat.ofNat_ne_zero, Polynomial.C_1,
          one_mul]
      _ = _ := by rw [hd, ← mul_assoc, ← Polynomial.C_mul, mul_comm (4 : ℚ)]

/-- Affine derivative coefficients from the original, unshifted profile row.
All cells can share that original row. -/
private def quarterDerivativeRow (N : ℕ) (row : Array ℚ) (l : ℚ) (j : ℕ) : Array ℚ :=
  Array.ofFn fun i : Fin (N - j + 1) ↦
    (4 : ℚ) ^ j * ((i.val + j).descFactorial j : ℚ) *
      ((1 / 4 : ℚ) ^ (i.val + j) *
        ∑ k ∈ Finset.range (N + 1),
          row[k]?.getD 0 * ((Nat.fast_choose k (i.val + j) : ℚ) * l ^ (k - (i.val + j))))

/-- The common denominator for the profile in a coordinate four times the
log coordinate. This denominator is shared by all quarter-width cells. -/
private def quarterProfileDen (N : ℕ) (row : Array ℚ) : ℕ :=
  (Finset.range (N + 1)).lcm fun k ↦ (row[k]?.getD 0 / (4 : ℚ) ^ k).den

/-- Clear the scaled profile coefficients before shifting to integer nodes. -/
private def quarterProfileIntRow (N : ℕ) (row : Array ℚ) : Array ℤ :=
  let D := quarterProfileDen N row
  Array.ofFn fun k : Fin (N + 1) ↦ clearedProfileCoeff D (row[k.val]?.getD 0 / (4 : ℚ) ^ k.val)

/-- Recover the scaled rational coefficient from the integer profile row. -/
private theorem quarter_profile_int_cast (N : ℕ) (row : Array ℚ) {k : ℕ} (hk : k < N + 1) :
    ((quarterProfileIntRow N row)[k]?.getD 0 : ℚ) =
      (quarterProfileDen N row : ℚ) * (row[k]?.getD 0 / (4 : ℚ) ^ k) := by
  let q := fun k : ℕ ↦ row[k]?.getD 0 / (4 : ℚ) ^ k
  let D := quarterProfileDen N row
  have h : (q k).den ∣ D := Finset.dvd_lcm (Finset.mem_range.mpr hk)
  simpa only [quarterProfileIntRow, getElem?_def, Array.size_ofFn, hk, dite_eq_left,
    Array.getElem_ofFn, Option.getD_some, q, D] using cleared_profile_coeff_cast D (q k) h

/-- Build a shared binomial table for the integer shifts. -/
private def shiftChooseTable (N : ℕ) : ℕ → ℕ → ℕ :=
  let rows :=
    Array.ofFn fun k : Fin (N + 1) ↦ Array.ofFn fun i : Fin (N + 1) ↦ Nat.fast_choose k.val i.val
  fun k i ↦ ((rows[k]?.getD #[])[i]?.getD 0)

/-- A lookup in the shared table agrees with the binomial coefficient. -/
private theorem shift_choose_eq (N : ℕ) {k i : ℕ} (hk : k < N + 1) :
    shiftChooseTable N k i = Nat.fast_choose k i := by
  by_cases hi : i < N + 1
  · simp only [shiftChooseTable, getElem?_def, Array.size_ofFn, hk, hi, dite_eq_left,
      Array.getElem_ofFn, Option.getD_some]
  · have hki : k < i := hk.trans_le (Nat.le_of_not_gt hi)
    simp only [shiftChooseTable, getElem?_def, Array.size_ofFn, hk, hi, dite_eq_left, dite_false,
      Array.getElem_ofFn, Option.getD_some, Option.getD_none, ← Nat.choose_eq_fast_choose,
      Nat.choose_eq_zero_of_lt hki]

/-- Powers of a cell node, shared across all shifted coefficient sums. -/
private def shiftPowerRow (N b : ℕ) : Array ℤ :=
  Array.ofFn fun i : Fin (N + 1) ↦ (b : ℤ) ^ i.val

/-- The power row supplies the exact value for every in-range exponent. -/
private theorem shift_power_eq (N b : ℕ) {i : ℕ} (hi : i < N + 1) :
    (shiftPowerRow N b)[i]?.getD 0 = (b : ℤ) ^ i := by
  simp only [shiftPowerRow, getElem?_def, Array.size_ofFn, hi, dite_eq_left, Array.getElem_ofFn,
    Option.getD_some]

/-- Shift the scaled integral profile to an integer node and differentiate
in the original log coordinate. The result is a numerator over the shared denominator. -/
private def quarterDerivativeNumerator (N : ℕ) (row : Array ℤ) (choose : ℕ → ℕ → ℕ)
    (powers : Array ℤ) (j i : ℕ) : ℤ :=
  4 ^ j * ((i + j).descFactorial j : ℤ) *
    ∑ k ∈ Finset.range (N + 1),
      row[k]?.getD 0 * ((choose k (i + j) : ℤ) * powers[k - (i + j)]?.getD 0)

/-- The integer numerator equals the original rational affine coefficient
after dividing by the common scaled denominator. -/
private theorem quarter_derivative_numerator_eq (N : ℕ) (row : Array ℚ) (b j i : ℕ)
    (hi : i < N - j + 1) :
    (quarterDerivativeNumerator N (quarterProfileIntRow N row) (shiftChooseTable N)
          (shiftPowerRow N b) j i :
        ℚ) =
      (quarterProfileDen N row : ℚ) * (quarterDerivativeRow N row ((b : ℚ) / 4) j)[i]?.getD 0 := by
  simp only [quarterDerivativeNumerator, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_natCast, Int.cast_sum, quarterDerivativeRow, getElem?_def, Array.size_ofFn, hi,
    dite_eq_left, Array.getElem_ofFn, Option.getD_some]
  rw [← mul_assoc, ← mul_assoc, mul_comm (quarterProfileDen N row : ℚ)]
  simp only [mul_assoc]
  congr 2
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hrow := quarter_profile_int_cast N row hk'
  simp only [getElem?_def] at hrow
  have hpowrow := shift_power_eq N b ((Nat.sub_le k (i + j)).trans_lt hk')
  simp only [getElem?_def] at hpowrow
  rw [hrow, shift_choose_eq N hk', hpowrow, Int.cast_pow, Int.cast_natCast]
  by_cases hki : i + j ≤ k
  · have hpow : (4 : ℚ) ^ k = 4 ^ (i + j) * 4 ^ (k - (i + j)) := by
      rw [← pow_add, Nat.add_sub_of_le hki]
    rw [hpow, div_pow, one_pow, div_pow]
    ring
  · simp only [← Nat.choose_eq_fast_choose, Nat.choose_eq_zero_of_lt (lt_of_not_ge hki),
      Nat.cast_zero, zero_mul, mul_zero]

/-- The derivative row before division by the shared profile denominator. -/
private def quarterNumeratorRow (N : ℕ) (row : Array ℤ) (choose : ℕ → ℕ → ℕ) (b j : ℕ) : Array ℤ :=
  let powers := shiftPowerRow N b
  Array.ofFn fun i : Fin (N - j + 1) ↦ quarterDerivativeNumerator N row choose powers j i

/-- Each integer entry is the corresponding rational derivative coefficient
times the positive common denominator. -/
private theorem quarter_numerator_row_cast (N : ℕ) (row : Array ℚ) (b j : ℕ) {i : ℕ}
    (hi : i < N - j + 1) :
    ((quarterNumeratorRow N (quarterProfileIntRow N row) (shiftChooseTable N) b j)[i]?.getD 0 : ℚ) =
      (quarterProfileDen N row : ℚ) * (quarterDerivativeRow N row ((b : ℚ) / 4) j)[i]?.getD 0 := by
  simpa only [quarterNumeratorRow, getElem?_def, Array.size_ofFn, hi, dite_eq_left,
    Array.getElem_ofFn, Option.getD_some] using quarter_derivative_numerator_eq N row b j i hi

/-- In-range entries of the computed row are the affine derivative coefficients. -/
private theorem quarter_derivative_coeff (K : HighGaussianKernel) (l : ℚ) {j i : ℕ}
    (hi : i ≤ 2 * K.degree + 3 - j) :
    (quarterDerivativeRow (2 * K.degree + 3) (K.cellPowerRow 0 1) l j)[i]?.getD 0 =
      (((Polynomial.derivative^[j]) K.ratProfile).comp
            (Polynomial.C (1 / 4) * Polynomial.X + Polynomial.C l)).coeff
        i := by
  have hi' := Nat.lt_succ_of_le hi
  rw [derivative_quarter_comp, Polynomial.coeff_C_mul, Polynomial.coeff_iterate_derivative,
    nsmul_eq_mul, high_rat_profile_affine_coeff]
  simp only [quarterDerivativeRow, Array.size_ofFn, getElem?_def, hi', dite_eq_left,
    Array.getElem_ofFn, Option.getD_some, mul_assoc]
  congr 3
  apply Finset.sum_congr rfl
  intro k hk
  change (K.cellPowerRow 0 1)[k]?.getD 0 * _ = _
  rw [high_cell_power_coeff K 0 1 (Finset.mem_range.mp hk), Polynomial.C_1, one_mul, Polynomial.C_0,
    add_zero, Polynomial.comp_X, high_rat_profile_coeff]

/-- The computed cell row supplies the clipped Bernstein coefficients of
the analytic derivative profile. -/
private theorem quarter_derivative_bernstein (K : HighGaussianKernel) (l : ℚ) (j i : ℕ) :
    let n := 2 * K.degree + 3 - j
    cellBernsteinFromPower n i (quarterDerivativeRow (2 * K.degree + 3) (K.cellPowerRow 0 1) l j) =
      Analysis.bernsteinRatCoeff
        (((Polynomial.derivative^[j]) K.ratProfile).comp
          (Polynomial.C (1 / 4) * Polynomial.X + Polynomial.C l))
        n i := by
  intro n
  simp only [cellBernsteinFromPower, Analysis.bernsteinRatCoeff]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hki : k ≤ i
  · rw [ite_eq_left hki, quarter_derivative_coeff K l (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
  · simp only [ite_eq_right hki, ← Nat.choose_eq_fast_choose,
      Nat.choose_eq_zero_of_lt (lt_of_not_ge hki), Nat.cast_zero, zero_div, mul_zero]

/-- Scale the variable in a cell coefficient row by a positive integer width. -/
private def scaleCellRow {R : Type*} [Semiring R] (n : ℕ) (row : Array R) (w : ℕ) : Array R :=
  Array.ofFn fun i : Fin (n + 1) ↦ row[i.val]?.getD 0 * (w : R) ^ i.val

/-- Reading an in-range scaled row entry supplies the intended power of the width. -/
private theorem scale_cell_row_get {R : Type*} [Semiring R] (n : ℕ) (row : Array R) (w : ℕ) {i : ℕ}
    (hi : i < n + 1) : (scaleCellRow n row w)[i]?.getD 0 = row[i]?.getD 0 * (w : R) ^ i := by
  simp only [scaleCellRow, getElem?_def, Array.size_ofFn, hi, dite_eq_left, Array.getElem_ofFn,
    Option.getD_some]

/-- Widening the normalized cell multiplies the coefficient of each power
by the same power of the integer width. -/
private theorem scaled_derivative_coeff (K : HighGaussianKernel) (l : ℚ) (j w : ℕ) {i : ℕ}
    (hi : i < 2 * K.degree + 3 - j + 1) :
    let n := 2 * K.degree + 3 - j
    let A := quarterDerivativeRow (2 * K.degree + 3) (K.cellPowerRow 0 1) l j
    (scaleCellRow n A w)[i]?.getD 0 =
      (((Polynomial.derivative^[j]) K.ratProfile).comp
            (Polynomial.C ((w : ℚ) / 4) * Polynomial.X + Polynomial.C l)).coeff
        i := by
  intro n A
  let L : Polynomial ℚ := Polynomial.C (1 / 4) * Polynomial.X + Polynomial.C l
  have hL :
    L.comp (Polynomial.C (w : ℚ) * Polynomial.X) =
      Polynomial.C ((w : ℚ) / 4) * Polynomial.X + Polynomial.C l := by
    simp only [L, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
    rw [← mul_assoc, ← Polynomial.C_mul, one_div, mul_comm (4 : ℚ)⁻¹, ← div_eq_mul_inv]
  rw [scale_cell_row_get n A w hi, quarter_derivative_coeff K l (Nat.le_of_lt_succ hi), ← hL, ←
    Polynomial.comp_assoc, Polynomial.comp_C_mul_X_coeff]

/-- Bernstein conversion of the scaled row agrees with the affine polynomial. -/
private theorem scaled_derivative_bernstein (K : HighGaussianKernel) (l : ℚ) (j w i : ℕ) :
    let n := 2 * K.degree + 3 - j
    let A := quarterDerivativeRow (2 * K.degree + 3) (K.cellPowerRow 0 1) l j
    cellBernsteinFromPower n i (scaleCellRow n A w) =
      Analysis.bernsteinRatCoeff
        (((Polynomial.derivative^[j]) K.ratProfile).comp
          (Polynomial.C ((w : ℚ) / 4) * Polynomial.X + Polynomial.C l))
        n i := by
  intro n A
  simp only [cellBernsteinFromPower, Analysis.bernsteinRatCoeff]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hki : k ≤ i
  · rw [ite_eq_left hki, scaled_derivative_coeff K l j w (Finset.mem_range.mp hk)]
  · simp only [ite_eq_right hki, ← Nat.choose_eq_fast_choose,
      Nat.choose_eq_zero_of_lt (lt_of_not_ge hki), Nat.cast_zero, zero_div, mul_zero]

/-- A common multiple of the Bernstein binomial denominators, independent
of the cell and available for reuse throughout the partition. -/
private def bernsteinBinomialDen (n : ℕ) (choose : ℕ → ℕ → ℕ) : ℕ :=
  (Finset.range (n + 1)).lcm (choose n)

/-- Precompute the integer factors that replace division by the Bernstein
binomial denominators. -/
private def bernsteinIntFactors (n : ℕ) (choose : ℕ → ℕ → ℕ) : Array ℕ :=
  let D := bernsteinBinomialDen n choose
  Array.ofFn fun k : Fin (n + 1) ↦ D / choose n k

/-- Within the Bernstein degree the common multiple is positive. -/
private theorem bernstein_binomial_den_pos {N n : ℕ} (hn : n ≤ N) :
    0 < bernsteinBinomialDen n (shiftChooseTable N) := by
  apply Nat.pos_of_ne_zero
  refine Finset.lcm_ne_zero_iff.mpr fun k hk ↦ ?_
  rw [shift_choose_eq N (Nat.lt_succ_of_le hn), ← Nat.choose_eq_fast_choose]
  exact (Nat.choose_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).ne'

/-- The precomputed factors implement exact multiplication by the common
multiple followed by division by the binomial coefficient. -/
private theorem bernstein_int_factor_cast {N n k : ℕ} (hn : n ≤ N) (hk : k < n + 1) :
    ((bernsteinIntFactors n (shiftChooseTable N))[k]?.getD 0 : ℚ) =
      (bernsteinBinomialDen n (shiftChooseTable N) : ℚ) / (Nat.fast_choose n k : ℚ) := by
  have hdiv : shiftChooseTable N n k ∣ bernsteinBinomialDen n (shiftChooseTable N) :=
    Finset.dvd_lcm (Finset.mem_range.mpr hk)
  have hpos : 0 < Nat.fast_choose n k := by
    rw [← Nat.choose_eq_fast_choose]
    exact Nat.choose_pos (Nat.le_of_lt_succ hk)
  apply (eq_div_iff (Nat.cast_ne_zero.mpr hpos.ne')).mpr
  simp only [bernsteinIntFactors, getElem?_def, Array.size_ofFn, hk, dite_eq_left,
    Array.getElem_ofFn, Option.getD_some]
  rw [← shift_choose_eq N (Nat.lt_succ_of_le hn), ← Nat.cast_mul, Nat.div_mul_cancel hdiv]

/-- Compute all clipped Bernstein numerators using precomputed integer factors. -/
private def clippedBernsteinInt (n : ℕ) (a : Array ℤ) (factors : Array ℕ) (choose : ℕ → ℕ → ℕ)
    (sign : ℤ) : ℤ :=
  let w := Array.ofFn fun k : Fin (n + 1) ↦ a[k.val]?.getD 0 * (factors[k.val]?.getD 0 : ℤ)
  ∑ i : Fin (n + 1),
    max 0 (-(sign * ∑ k ∈ Finset.range (i.val + 1), w[k]?.getD 0 * (choose i.val k : ℤ)))

/-- The clipped integer sum is the rational sum scaled by the common
profile denominator and the shared binomial denominator. -/
private theorem clipped_bernstein_int_eq {N n : ℕ} (hn : n ≤ N) (a : Array ℤ) (row : Array ℚ)
    (sign : ℤ) {D : ℕ} (hD : 0 < D)
    (ha : ∀ k < n + 1, (a[k]?.getD 0 : ℚ) = (D : ℚ) * row[k]?.getD 0) :
    (clippedBernsteinInt n a (bernsteinIntFactors n (shiftChooseTable N)) (shiftChooseTable N)
            sign :
          ℚ) /
        ((D : ℚ) * bernsteinBinomialDen n (shiftChooseTable N)) =
      ∑ i : Fin (n + 1), max 0 (-((sign : ℚ) * cellBernsteinFromPower n i row)) := by
  let C := bernsteinBinomialDen n (shiftChooseTable N)
  let factors := bernsteinIntFactors n (shiftChooseTable N)
  let w := Array.ofFn fun k : Fin (n + 1) ↦ a[k.val]?.getD 0 * (factors[k.val]?.getD 0 : ℤ)
  let b := fun i : Fin (n + 1) ↦
    ∑ k ∈ Finset.range (i.val + 1), w[k]?.getD 0 * (shiftChooseTable N i.val k : ℤ)
  have hDC : (0 : ℚ) < (D : ℚ) * C :=
    mul_pos (Nat.cast_pos.mpr hD) (Nat.cast_pos.mpr (bernstein_binomial_den_pos hn))
  have hB (i : Fin (n + 1)) : (b i : ℚ) / ((D : ℚ) * C) = cellBernsteinFromPower n i row := by
    apply (div_eq_iff hDC.ne').mpr
    simp only [b, Int.cast_sum, Int.cast_mul, Int.cast_natCast, cellBernsteinFromPower,
      Finset.sum_mul]
    rw [←
      Finset.sum_subset
        (Finset.range_subset_range.mpr (Nat.succ_le_succ (Nat.le_of_lt_succ i.isLt)))]
    · apply Finset.sum_congr rfl
      intro k hk
      have hki := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hkn := (Finset.mem_range.mp hk).trans_le (Nat.succ_le_succ (Nat.le_of_lt_succ i.isLt))
      rw [ite_eq_left hki, shift_choose_eq N (i.isLt.trans_le (Nat.succ_le_succ hn))]
      have hw : w[k]?.getD 0 = a[k]?.getD 0 * (factors[k]?.getD 0 : ℤ) := by
        simp only [w, getElem?_def, Array.size_ofFn, hkn, dite_eq_left, Array.getElem_ofFn,
          Option.getD_some]
      rw [hw, Int.cast_mul, Int.cast_natCast, ha k hkn, bernstein_int_factor_cast hn hkn]
      dsimp only [C]
      ring
    · intro k _ hk
      have hki : ¬k ≤ i.val := fun h ↦ hk (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
      rw [ite_eq_right hki, zero_mul]
  change (((∑ i : Fin (n + 1), max 0 (-(sign * b i)) : ℤ) : ℚ) / ((D : ℚ) * C)) = _
  rw [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Int.cast_max, Int.cast_zero, Int.cast_neg, ← max_div_div_right hDC.le, zero_div, neg_div,
    Int.cast_mul, mul_div_assoc, hB]

/-- Check whether all Bernstein coefficients are nonnegative on the cell
from `b/4` to `(b+w)/4`, using the integer shift and conversion. -/
public def highProfileCellSign (K : HighGaussianKernel) (j b w : ℕ) (sign : ℤ) : Bool :=
  let N := 2 * K.degree + 3
  let n := N - j
  let choose := shiftChooseTable N
  let row := quarterProfileIntRow N (K.cellPowerRow 0 1)
  let a := scaleCellRow n (quarterNumeratorRow N row choose b j) w
  decide (clippedBernsteinInt n a (bernsteinIntFactors n choose) choose sign = 0)

/-- Check the nonnegative sign on the entire cell. -/
public def highProfileCellNonneg (K : HighGaussianKernel) (j b w : ℕ) : Bool :=
  highProfileCellSign K j b w 1

/-- The integer check certifies the sign of the derivative across the
entire widened cell, including its endpoints. -/
private theorem high_profile_cell_coeff_sign (K : HighGaussianKernel) (j b w : ℕ) (sign : ℤ)
    (h : highProfileCellSign K j b w sign = true) :
    let P := (Polynomial.derivative^[j]) K.ratProfile
    let n := 2 * K.degree + 3 - j
    ∀ i : Fin (n + 1),
      0 ≤
        (sign : ℚ) *
          Analysis.bernsteinRatCoeff
            (P.comp (Polynomial.C ((w : ℚ) / 4) * Polynomial.X + Polynomial.C ((b : ℚ) / 4))) n
            i := by
  let N := 2 * K.degree + 3
  let n := N - j
  let R := K.cellPowerRow 0 1
  let a :=
    scaleCellRow n (quarterNumeratorRow N (quarterProfileIntRow N R) (shiftChooseTable N) b j) w
  let A := scaleCellRow n (quarterDerivativeRow N R ((b : ℚ) / 4) j) w
  let D := quarterProfileDen N R
  have hD : 0 < D :=
    Nat.pos_of_ne_zero
      (Finset.lcm_ne_zero_iff.mpr fun k _ ↦ (R[k]?.getD 0 / (4 : ℚ) ^ k).den_ne_zero)
  have ha (k : ℕ) (hk : k < n + 1) : (a[k]?.getD 0 : ℚ) = (D : ℚ) * A[k]?.getD 0 := by
    dsimp only [a, A]
    rw [scale_cell_row_get n _ w hk, scale_cell_row_get n _ w hk, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, quarter_numerator_row_cast N R b j hk, mul_assoc]
  have hsum := clipped_bernstein_int_eq (Nat.sub_le N j) a A sign hD ha
  have hzero :
    clippedBernsteinInt n a (bernsteinIntFactors n (shiftChooseTable N)) (shiftChooseTable N) sign =
      0 :=
    of_decide_eq_true h
  rw [hzero, Int.cast_zero, zero_div] at hsum
  intro P n' i
  rw [← scaled_derivative_bernstein K ((b : ℚ) / 4) j w i]
  change 0 ≤ (sign : ℚ) * cellBernsteinFromPower n i A
  have hcoeff : 0 ≤ (sign : ℚ) * cellBernsteinFromPower n i A := by
    have hle :=
      Finset.single_le_sum (f := fun k : Fin (n + 1) ↦
        max 0 (-((sign : ℚ) * cellBernsteinFromPower n k A))) (fun k _ ↦ le_max_left _ _)
        (Finset.mem_univ i)
    exact neg_nonpos.mp ((le_max_right 0 _).trans (hle.trans_eq hsum.symm))
  exact hcoeff

/-- The integer nonnegative test certifies the entire widened cell. -/
public theorem high_profile_cell_nonneg (K : HighGaussianKernel) (j b w : ℕ) (hw : 0 < w)
    (h : highProfileCellNonneg K j b w = true) :
    ∀ t ∈ Set.Icc ((b : ℝ) / 4) (((b + w : ℕ) : ℝ) / 4),
      0 ≤ ((Polynomial.derivative^[j]) K.realProfile).eval t := by
  let P := (Polynomial.derivative^[j]) K.ratProfile
  let n := 2 * K.degree + 3 - j
  have hp : P.natDegree ≤ n :=
    (Polynomial.natDegree_iterate_derivative _ _).trans
      (Nat.sub_le_sub_right (high_rat_profile_degree K) j)
  have hab : (b : ℚ) / 4 < ((b + w : ℕ) : ℚ) / 4 := by
    exact div_lt_div_of_pos_right (Nat.cast_lt.mpr (Nat.lt_add_of_pos_right hw)) (by norm_num only)
  have hwidth : ((b + w : ℕ) : ℚ) / 4 - (b : ℚ) / 4 = (w : ℚ) / 4 := by
    rw [Nat.cast_add]
    ring
  have hP :=
    bernstein_cell_nonneg P hp hab
      (by
        intro i
        rw [hwidth]
        change
          0 ≤
            Analysis.bernsteinRatCoeff
              (((Polynomial.derivative^[j]) K.ratProfile).comp
                (Polynomial.C ((w : ℚ) / 4) * Polynomial.X + Polynomial.C ((b : ℚ) / 4)))
              n i
        simpa only [Int.cast_one, one_mul] using high_profile_cell_coeff_sign K j b w 1 h i)
  simpa only [P, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    ← Polynomial.iterate_derivative_map, high_comp_profile_map] using hP

/-- A successful test of the negative sign certifies the profile is
nonpositive on the entire closed cell. -/
public theorem high_profile_cell_nonpos (K : HighGaussianKernel) (j b w : ℕ) (hw : 0 < w)
    (h : highProfileCellSign K j b w (-1) = true) :
    ∀ t ∈ Set.Icc ((b : ℝ) / 4) (((b + w : ℕ) : ℝ) / 4),
      ((Polynomial.derivative^[j]) K.realProfile).eval t ≤ 0 := by
  let P := (Polynomial.derivative^[j]) K.ratProfile
  let n := 2 * K.degree + 3 - j
  have hp : P.natDegree ≤ n :=
    (Polynomial.natDegree_iterate_derivative _ _).trans
      (Nat.sub_le_sub_right (high_rat_profile_degree K) j)
  have hab : (b : ℚ) / 4 < ((b + w : ℕ) : ℚ) / 4 :=
    div_lt_div_of_pos_right (Nat.cast_lt.mpr (Nat.lt_add_of_pos_right hw)) (by norm_num only)
  have hwidth : ((b + w : ℕ) : ℚ) / 4 - (b : ℚ) / 4 = (w : ℚ) / 4 := by
    rw [Nat.cast_add]
    ring
  have hP :=
    bernstein_cell_nonpos P hp hab
      (by
        intro i
        rw [hwidth]
        exact
          neg_nonneg.mp
            (by
              simpa only [Int.cast_neg, Int.cast_one, neg_one_mul] using
                high_profile_cell_coeff_sign K j b w (-1) h i))
  simpa only [P, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    ← Polynomial.iterate_derivative_map, high_comp_profile_map] using hP

/-- Compute the signed Laplace factor at a quarter-unit endpoint directly
from the shifted integer derivative coefficients. -/
public def highSignedEndpointFactor (K : HighGaussianKernel) (j b : ℕ) : ℚ :=
  let N := 2 * K.degree + 3
  let n := N - j
  let R := K.cellPowerRow 0 1
  let D := quarterProfileDen N R
  let A := quarterNumeratorRow N (quarterProfileIntRow N R) (shiftChooseTable N) b j
  let d := K.pole - 1 / 2
  ∑ k ∈ Finset.range (n + 1), ((A[k]?.getD 0 : ℚ) / D * 4 ^ k) * ((k.factorial : ℚ) / d ^ (k + 1))

/-- The executable endpoint factor equals the signed analytic polynomial moment. -/
public theorem high_signed_endpoint_factor_eq (K : HighGaussianKernel) (j b : ℕ) :
    highSignedEndpointFactor K j b =
      signedTailFactor ((Polynomial.derivative^[j]) K.ratProfile) (K.pole - 1 / 2)
        ((b : ℚ) / 4) := by
  let P := (Polynomial.derivative^[j]) K.ratProfile
  let n := 2 * K.degree + 3 - j
  let l := (b : ℚ) / 4
  have hn : P.natDegree ≤ n :=
    (Polynomial.natDegree_iterate_derivative _ _).trans
      (Nat.sub_le_sub_right (high_rat_profile_degree K) j)
  have hc : (P.comp (Polynomial.X + Polynomial.C l)).natDegree ≤ n := by
    have h := Analysis.bernstein_affine_degree P n hn l (l + 1)
    simpa only [add_sub_cancel_left, Polynomial.C_1, one_mul] using h
  rw [signed_tail_factor_sum P _ l n hc, highSignedEndpointFactor]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hD : (quarterProfileDen (2 * K.degree + 3) (K.cellPowerRow 0 1) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (Finset.lcm_ne_zero_iff.mpr fun i _ ↦
        ((K.cellPowerRow 0 1)[i]?.getD 0 / (4 : ℚ) ^ i).den_ne_zero)
  have hs :=
    (scale_cell_row_get n (quarterDerivativeRow (2 * K.degree + 3) (K.cellPowerRow 0 1) l j) 4
        hk').symm
  norm_num only [Nat.cast_ofNat] at hs
  rw [quarter_numerator_row_cast _ _ _ _ hk', mul_comm (quarterProfileDen _ _ : ℚ),
    mul_div_cancel_right₀ _ hD, hs, scaled_derivative_coeff K l j 4 hk']
  norm_num only [P, Nat.cast_ofNat, div_self, OfNat.ofNat_ne_zero, Polynomial.C_1, one_mul]

/-- Executable rational charge for a nonpositive cell, obtained by
subtracting a lower bound at the left endpoint from an upper bound at the right. -/
public def highNonposCellCharge (K : HighGaussianKernel) (j b w : ℕ) : ℚ :=
  let d := K.pole - 1 / 2
  let xa := d * ((b : ℚ) / 4)
  let xz := d * (((b + w : ℕ) : ℚ) / 4)
  let F := highSignedEndpointFactor K j b
  let G := highSignedEndpointFactor K j (b + w)
  max (negativeEndpointExpLower xz * G) (negativeEndpointExpUpper xz * G) -
    min (negativeEndpointExpLower xa * F) (negativeEndpointExpUpper xa * F)

/-- On a checked nonpositive high-kernel cell, use rational endpoint
charges in place of a quarter-cell Bernstein sum. -/
public theorem high_nonpos_cell_endpoint_le (K : HighGaussianKernel) (j b w : ℕ) (hw : 0 < w)
    (hb : b + w ≤ 320) (h : highProfileCellSign K j b w (-1) = true) :
    let R := (Polynomial.derivative^[j]) K.realProfile
    let d := K.pole - 1 / 2
    let a := (b : ℚ) / 4
    let z := ((b + w : ℕ) : ℚ) / 4
    (∫ t in (a : ℝ)..(z : ℝ), Real.exp (-(d : ℝ) * t) * max 0 (-R.eval t)) ≤
      (highNonposCellCharge K j b w : ℝ) := by
  intro R d a z
  let L := fun t ↦ negativeEndpointExpLower (d * t)
  let U := fun t ↦ negativeEndpointExpUpper (d * t)
  let P := (Polynomial.derivative^[j]) K.ratProfile
  have hd : 0 < d := by cases K <;> norm_num only [d, HighGaussianKernel.pole]
  have hd' : d ≤ 11 / 4 := by cases K <;> norm_num only [d, HighGaussianKernel.pole]
  have ha : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have haz : a ≤ z :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.le_add_right b w)) (by norm_num only)
  have hz : z ≤ 80 := by
    dsimp only [z]
    exact
      (div_le_div_of_nonneg_right (Nat.cast_le.mpr hb) (by norm_num only)).trans_eq
        (by norm_num only)
  have hE (x : ℚ) (hx : 0 ≤ x) (h₈ : x ≤ 80) :
    (L x : ℝ) ≤ Real.exp (-(d : ℝ) * (x : ℝ)) ∧ Real.exp (-(d : ℝ) * (x : ℝ)) ≤ (U x : ℝ) := by
    have hdx := mul_nonneg hd.le hx
    have hcap : d * x ≤ 264 := (mul_le_mul hd' h₈ hx (by norm_num only)).trans (by norm_num only)
    simpa only [L, U, Rat.cast_mul, neg_mul] using
      And.intro (negative_endpoint_exp_lower_valid hdx hcap) (negative_endpoint_exp_upper_valid hdx)
  have hmap : P.map (Rat.castHom ℝ) = R := by
    dsimp only [P, R]
    rw [← Polynomial.iterate_derivative_map, high_comp_profile_map]
  have hP : ∀ t ∈ Set.Icc (a : ℝ) (z : ℝ), (P.map (Rat.castHom ℝ)).eval t ≤ 0 := by
    rw [hmap]
    simpa only [a, z, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      high_profile_cell_nonpos K j b w hw h
  simpa only [hmap, highNonposCellCharge, high_signed_endpoint_factor_eq] using
    negative_cell_le_endpoint_ranges P hd ha haz hP (L a) (U a) (L z) (U z) (hE a ha (haz.trans hz))
      (hE z (ha.trans haz) hz)

/-- Compute one H28 charge, sharing the affine row across Bernstein coefficients. -/
private def computedNegativeCell (K : HighGaussianKernel) (D C : ℕ) (row : Array ℤ)
    (choose : ℕ → ℕ → ℕ) (factors : Array ℕ) (j i : ℕ) : ℚ :=
  let n := 2 * K.degree + 3 - j
  let s := K.pole - 1 / 2
  let l := correctionNode K i
  let a := quarterNumeratorRow (2 * K.degree + 3) row choose (correctionTick K i) j
  Analysis.compensationExpUpper (s * l) *
    (1 / 4 * ((clippedBernsteinInt n a factors choose 1 : ℚ) / ((D : ℚ) * C) / ((n : ℚ) + 1)))

/-- Evaluate a finite block without constructing derivative polynomials. -/
private def computedNegativeBlock (K : HighGaussianKernel) (j start count : ℕ) : ℚ :=
  let row := K.cellPowerRow 0 1
  let N := 2 * K.degree + 3
  let D := quarterProfileDen N row
  let a := quarterProfileIntRow N row
  let choose := shiftChooseTable N
  let C := bernsteinBinomialDen (N - j) choose
  let factors := bernsteinIntFactors (N - j) choose
  ∑ i ∈ Finset.range count, computedNegativeCell K D C a choose factors j (start + i)

/-- Evaluate the full finite H28 charge using the integer coefficient tables. -/
public def computedHighNegativeCharge (K : HighGaussianKernel) (j : ℕ) : ℚ :=
  computedNegativeBlock K j 0 (correctionCellCount K)

/-- The executable block charge equals the analytic Bernstein sum. -/
private theorem computed_negative_block_eq (K : HighGaussianKernel) (j start count : ℕ) :
    computedNegativeBlock K j start count = negativeBlockCharge K j start count := by
  simp only [computedNegativeBlock, computedNegativeCell, negativeBlockCharge]
  apply Finset.sum_congr rfl
  intro i _
  have hw : correctionNode K (start + (i + 1)) - correctionNode K (start + i) = 1 / 4 := by
    simp only [correctionNode, Nat.cast_add, Nat.cast_one]
    ring
  have hD : 0 < quarterProfileDen (2 * K.degree + 3) (K.cellPowerRow 0 1) :=
    Nat.pos_of_ne_zero
      (Finset.lcm_ne_zero_iff.mpr fun k _ ↦
        ((K.cellPowerRow 0 1)[k]?.getD 0 / (4 : ℚ) ^ k).den_ne_zero)
  rw [clipped_bernstein_int_eq (Nat.sub_le _ _) _ _ 1 hD
      (fun k hk ↦ quarter_numerator_row_cast _ _ _ _ hk)]
  simp only [hw, correction_tick_eq, quarter_derivative_bernstein, Int.cast_one, one_mul]

/-- The executable charge equals the rational analytic charge for each derivative. -/
public theorem computed_high_negative_charge_eq (K : HighGaussianKernel) (j : ℕ) :
    computedHighNegativeCharge K j = highNegativeMomentCharge K j := by
  exact computed_negative_block_eq K j 0 (correctionCellCount K)

/-- Sum a contiguous block of H28 cells, rounding each charge upward to
millionths. The block can be checked separately by the kernel. -/
public def highNegativeBlockTicks (K : HighGaussianKernel) (j start count : ℕ) : ℤ :=
  let row := K.cellPowerRow 0 1
  let N := 2 * K.degree + 3
  let D := quarterProfileDen N row
  let a := quarterProfileIntRow N row
  let choose := shiftChooseTable N
  let C := bernsteinBinomialDen (N - j) choose
  let factors := bernsteinIntFactors (N - j) choose
  ∑ i ∈ Finset.range count, ⌈10 ^ 6 * computedNegativeCell K D C a choose factors j (start + i)⌉

/-- Adjacent blocks add to the charge of their union. -/
public theorem high_negative_blocks_add (K : HighGaussianKernel) (j start m n : ℕ) :
    highNegativeBlockTicks K j start (m + n) =
      highNegativeBlockTicks K j start m + highNegativeBlockTicks K j (start + m) n := by
  simp only [highNegativeBlockTicks, Finset.sum_range_add, Nat.add_assoc]

/-- Sum the rounded charges for the full H28 partition. -/
public def highNegativeChargeTicks (K : HighGaussianKernel) (j : ℕ) : ℤ :=
  highNegativeBlockTicks K j 0 (correctionCellCount K)

/-- The full partition consists of 120 quarter-width cells for K186. -/
public theorem k186_negative_ticks_eq (j : ℕ) :
    highNegativeChargeTicks .k186 j = highNegativeBlockTicks .k186 j 0 120 := by rfl

/-- The full partition consists of 150 quarter-width cells for K196. -/
public theorem k196_negative_ticks_eq (j : ℕ) :
    highNegativeChargeTicks .k196 j = highNegativeBlockTicks .k196 j 0 150 := by rfl

/-- The integer sum bounds the analytic block charge after applying its scale. -/
private theorem negative_block_le_ticks (K : HighGaussianKernel) (j start count : ℕ) :
    negativeBlockCharge K j start count ≤
      (highNegativeBlockTicks K j start count : ℚ) / 10 ^ 6 := by
  rw [← computed_negative_block_eq K j start count, computedNegativeBlock, highNegativeBlockTicks,
    Int.cast_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  apply (le_div_iff₀ (by norm_num only : (0 : ℚ) < 10 ^ 6)).mpr
  rw [mul_comm _ (10 ^ 6 : ℚ)]
  exact Int.le_ceil _

/-- The scaled integer sum bounds the full analytic charge. -/
public theorem high_negative_charge_le_ticks (K : HighGaussianKernel) (j : ℕ) :
    highNegativeMomentCharge K j ≤ (highNegativeChargeTicks K j : ℚ) / 10 ^ 6 := by
  exact negative_block_le_ticks K j 0 (correctionCellCount K)

/-- The quarter-width Bernstein charges bound the negative correction over a block. -/
private theorem negative_moment_block_le (K : HighGaussianKernel) (j start count : ℕ) :
    let P := (Polynomial.derivative^[j]) K.realProfile
    let s := (K.pole : ℝ) - 1 / 2
    (∫ t in (correctionNode K start : ℝ)..(correctionNode K (start + count) : ℝ),
        Real.exp (-s * t) * max 0 (-P.eval t)) ≤
      (negativeBlockCharge K j start count : ℝ) := by
  intro P s
  let Q := (Polynomial.derivative^[j]) K.ratProfile
  let p := fun i ↦ correctionNode K (start + i)
  let d := K.pole - 1 / 2
  have hd : (d : ℝ) = s := by
    simp only [d, s, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  have hs : 0 ≤ s := sub_nonneg.mpr (high_gaussian_pole_gt K).le
  have hp (i : ℕ) : p i < p (i + 1) := by
    simp only [p, correctionNode, Nat.cast_add, Nat.cast_one]
    linarith only
  have hp₀ (i : ℕ) : 0 ≤ p i := by
    have hstart : 0 ≤ profileCorrectionStart K := by
      cases K <;> norm_num only [profileCorrectionStart]
    exact add_nonneg hstart (div_nonneg (Nat.cast_nonneg _) (by norm_num only))
  have he (i : ℕ) : Real.exp (-s * (p i : ℝ)) ≤ (Analysis.compensationExpUpper (d * p i) : ℝ) := by
    have hd₀ : 0 ≤ d := Rat.cast_nonneg.mp (hd.symm ▸ hs)
    simpa only [Rat.cast_mul, hd, neg_mul] using
      Analysis.compensation_exp_upper_valid (mul_nonneg hd₀ (hp₀ i))
  have hQ : Q.natDegree ≤ 2 * K.degree + 3 - j :=
    (Polynomial.natDegree_iterate_derivative K.ratProfile j).trans
      (Nat.sub_le_sub_right (high_rat_profile_degree K) j)
  have h :=
    Analysis.weighted_negative_bernstein Q count _ hQ hs p
      (fun i ↦ Analysis.compensationExpUpper (d * p i)) (fun i _ ↦ hp i) (fun i _ ↦ he i)
  have hcast (t : ℝ) : Q.eval₂ (Rat.castHom ℝ) t = P.eval t := by
    dsimp only [Q, P]
    rw [← Polynomial.eval_map, ← Polynomial.iterate_derivative_map, high_comp_profile_map]
  simpa only [hcast, negativeBlockCharge, Q, p, d, Nat.add_zero] using h

/-- The quarter-width Bernstein charges bound the full finite H28
negative correction at the kernel's decay rate. -/
public theorem high_negative_moment_le (K : HighGaussianKernel) (j : ℕ) :
    let P := (Polynomial.derivative^[j]) K.realProfile
    let s := (K.pole : ℝ) - 1 / 2
    (∫ t in (profileCorrectionStart K : ℝ)..(profileCorrectionEnd K : ℝ),
        Real.exp (-s * t) * max 0 (-P.eval t)) ≤
      (highNegativeMomentCharge K j : ℝ) := by
  have hstart : correctionNode K 0 = profileCorrectionStart K := by
    simp only [correctionNode, Nat.cast_zero, zero_div, add_zero]
  have hend :
    (correctionNode K (0 + correctionCellCount K) : ℝ) = (profileCorrectionEnd K : ℝ) := by
    cases K <;>
      norm_num only [correctionNode, correctionCellCount, profileCorrectionStart,
        profileCorrectionEnd, Nat.zero_add, Rat.cast_add, Rat.cast_div, Rat.cast_natCast,
        Rat.cast_ofNat, Int.cast_ofNat]
  simpa only [hstart, hend, highNegativeMomentCharge] using
    negative_moment_block_le K j 0 (correctionCellCount K)

/-- An upper bound on a contiguous block of rounded cell charges bounds
the weighted negative integral between its quarter-unit endpoints. -/
public theorem high_negative_block_integral_le (K : HighGaussianKernel) (j start count : ℕ) {M : ℤ}
    (hM : highNegativeBlockTicks K j start count ≤ M) :
    let P := (Polynomial.derivative^[j]) K.realProfile
    let s := (K.pole : ℝ) - 1 / 2
    let a := (profileCorrectionStart K : ℝ) + (start : ℝ) / 4
    let b := (profileCorrectionStart K : ℝ) + ((start + count : ℕ) : ℝ) / 4
    (∫ t in a..b, Real.exp (-s * t) * max 0 (-P.eval t)) ≤ (M : ℝ) / 10 ^ 6 := by
  intro P s a b
  have h := negative_moment_block_le K j start count
  have hrat :=
    (negative_block_le_ticks K j start count).trans
      (div_le_div_of_nonneg_right (Int.cast_le.mpr hM) (by norm_num only))
  have hreal : (negativeBlockCharge K j start count : ℝ) ≤ (M : ℝ) / 10 ^ 6 := by
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_le.mpr hrat : (negativeBlockCharge K j start count : ℝ) ≤ _)
  simpa only [correctionNode, Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
    h.trans hreal

/-- If the outer parts of the correction interval are nonnegative, only
the intervening block needs an integer bound on its negative moment. -/
public theorem high_negative_moment_le_middle (K : HighGaussianKernel) (j start count : ℕ) {M : ℤ}
    (hM : highNegativeBlockTicks K j start count ≤ M)
    (hb :
      (profileCorrectionStart K : ℝ) + ((start + count : ℕ) : ℝ) / 4 ≤
        (profileCorrectionEnd K : ℝ)) :
    let P := (Polynomial.derivative^[j]) K.realProfile
    let a₀ := (profileCorrectionStart K : ℝ)
    let b₀ := (profileCorrectionEnd K : ℝ)
    let a := a₀ + (start : ℝ) / 4
    let b := a₀ + ((start + count : ℕ) : ℝ) / 4
    (∀ t ∈ Set.Icc a₀ a, 0 ≤ P.eval t) →
      (∀ t ∈ Set.Icc b b₀, 0 ≤ P.eval t) → highNegativeMoment K j ≤ (M : ℝ) / 10 ^ 6 := by
  intro P a₀ b₀ a b haP hbP
  let s := (K.pole : ℝ) - 1 / 2
  let f := fun t : ℝ ↦ Real.exp (-s * t) * max 0 (-P.eval t)
  have hf : Continuous f := by
    unfold f; fun_prop
  have ha : a₀ ≤ a := le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) (by norm_num only))
  change (∫ t in a₀..b₀, f t) ≤ _
  rw [←
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable a₀ b)
      (hf.intervalIntegrable b b₀),
    ←
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable a₀ a)
      (hf.intervalIntegrable a b)]
  have h₀ : (∫ t in a₀..a, f t) = 0 := negative_moment_eq_zero P s ha haP
  have h₁ : (∫ t in b..b₀, f t) = 0 := negative_moment_eq_zero P s hb hbP
  rw [h₀, h₁, zero_add, add_zero]
  exact high_negative_block_integral_le K j start count hM

/-- For K186, checked nonnegative prefix and suffix cells reduce the
full negative moment on `[35,65]` to the intervening quarter-width block. -/
public theorem k186_negative_moment_le_compressed (j start count : ℕ) (hstart : 0 < start)
    (he : start + count < 120) (hleft : highProfileCellNonneg .k186 j 140 start = true)
    (hright : highProfileCellNonneg .k186 j (140 + (start + count)) (120 - (start + count)) = true)
    {M : ℤ} (hM : highNegativeBlockTicks .k186 j start count ≤ M) :
    highNegativeMoment .k186 j ≤ (M : ℝ) / 10 ^ 6 := by
  have hx : (0 : ℝ) < 4 := by norm_num only
  have hb :
    (profileCorrectionStart .k186 : ℝ) + ((start + count : ℕ) : ℝ) / 4 ≤
      (profileCorrectionEnd .k186 : ℝ) := by
    have h :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr he.le : ((start + count : ℕ) : ℝ) ≤ 120) hx.le
    norm_num only [profileCorrectionStart, profileCorrectionEnd, Rat.cast_ofNat, Int.cast_ofNat]
    linarith only [h]
  apply high_negative_moment_le_middle .k186 j start count hM hb
  · have h := high_profile_cell_nonneg .k186 j 140 start hstart hleft
    simpa only [profileCorrectionStart, Rat.cast_ofNat, Nat.cast_add, Nat.cast_ofNat, add_div,
      show (140 : ℝ) / 4 = 35 by norm_num only] using h
  · have h :=
      high_profile_cell_nonneg .k186 j (140 + (start + count)) (120 - (start + count))
        (Nat.sub_pos_of_lt he) hright
    have hsum : 140 + (start + count) + (120 - (start + count)) = 260 := by
      rw [Nat.add_assoc, Nat.add_sub_of_le he.le]
    simpa only [profileCorrectionStart, profileCorrectionEnd, Rat.cast_ofNat, Int.cast_ofNat, hsum,
      Nat.cast_add, Nat.cast_ofNat, add_div, show (140 : ℝ) / 4 = 35 by norm_num only,
      show (260 : ℝ) / 4 = 65 by norm_num only] using h

/-- Combine zero charges on nonnegative cells, endpoint charges on
nonpositive cells, and rounded unit-cell charges on the remaining cells.
The endpoints are given in quarter units. -/
public theorem high_negative_partition_le (K : HighGaussianKernel) (j N : ℕ) (p : ℕ → ℕ) (q : ℕ → ℚ)
    (hp : Monotone p) (hstep : ∀ i < N, p i < p (i + 1))
    (hstart : (p 0 : ℝ) / 4 = (profileCorrectionStart K : ℝ))
    (hend : (p N : ℝ) / 4 = (profileCorrectionEnd K : ℝ)) (hcap : p N ≤ 320)
    (hcert :
      ∀ i < N,
        let b := p i;
        let w := p (i + 1) - b;
        (highProfileCellNonneg K j b w = true ∧ 0 ≤ q i) ∨
          (highProfileCellSign K j b w (-1) = true ∧ highNonposCellCharge K j b w ≤ q i) ∨
          ((highNegativeBlockTicks K j (b - p 0) w : ℚ) / 10 ^ 6 ≤ q i)) :
    highNegativeMoment K j ≤ ((∑ i ∈ Finset.range N, q i) : ℚ) := by
  let P := (Polynomial.derivative^[j]) K.realProfile
  let d := (K.pole : ℝ) - 1 / 2
  let f := fun t : ℝ ↦ Real.exp (-d * t) * max 0 (-P.eval t)
  let x := fun i ↦ (p i : ℝ) / 4
  have hf : Continuous f := by
    unfold f; fun_prop
  change (∫ t in (profileCorrectionStart K : ℝ)..(profileCorrectionEnd K : ℝ), f t) ≤ _
  rw [← hstart, ← hend, Rat.cast_sum]
  change (∫ t in x 0..x N, f t) ≤ _
  rw [←
    intervalIntegral.sum_integral_adjacent_intervals
      (fun i _ ↦ hf.intervalIntegrable (x i) (x (i + 1)))]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  let b := p i
  let w := p (i + 1) - b
  have hw : 0 < w := Nat.sub_pos_of_lt (hstep i hi')
  have hbw : b + w = p (i + 1) := Nat.add_sub_of_le (hstep i hi').le
  have hxy : x i ≤ x (i + 1) :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr (hstep i hi').le) (by norm_num only)
  rcases hcert i hi' with ⟨h, hq⟩ | ⟨h, hq⟩ | hq
  · have hsign := high_profile_cell_nonneg K j b w hw h
    rw [hbw] at hsign
    rw [negative_moment_eq_zero P d hxy hsign]
    exact Rat.cast_nonneg.mpr hq
  · have hlast : b + w ≤ 320 := by
      rw [hbw]
      exact (hp (Nat.succ_le_of_lt hi')).trans hcap
    have hcell := high_nonpos_cell_endpoint_le K j b w hw hlast h
    dsimp only at hcell
    rw [hbw] at hcell
    have hreal : ((K.pole - 1 / 2 : ℚ) : ℝ) = d := by
      simp only [d, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    rw [hreal] at hcell
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      hcell.trans (Rat.cast_le.mpr hq)
  · let t := b - p 0
    let m := highNegativeBlockTicks K j t w
    have hcell := high_negative_block_integral_le K j t w (le_refl m)
    have hcoord (k : ℕ) :
      (profileCorrectionStart K : ℝ) + (k : ℝ) / 4 = ((p 0 + k : ℕ) : ℝ) / 4 := by
      rw [← hstart, Nat.cast_add, add_div]
    have ht : p 0 + t = b := Nat.add_sub_of_le (hp (Nat.zero_le i))
    have htt : p 0 + (t + w) = p (i + 1) := by rw [← Nat.add_assoc, ht, hbw]
    dsimp only at hcell
    rw [hcoord t, hcoord (t + w), ht, htt] at hcell
    refine hcell.trans ?_
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_le.mpr hq : ((((m : ℚ) / 10 ^ 6 : ℚ) : ℝ) ≤ (q i : ℝ)))

/-- H28 bounds the absolute tail by the exact signed moments and the
negative moment on the finite correction interval. -/
public theorem high_abs_tail_le_negative (K : HighGaussianKernel)
    (h : highIntProfileSignCheck K (profileCorrectionEnd K) = true) (j : ℕ) {z : ℝ}
    (hz : (profileCorrectionStart K : ℝ) ≤ z) :
    let P := (Polynomial.derivative^[j]) K.realProfile
    let Q := P.comp (Polynomial.X + Polynomial.C z)
    let s := (K.pole : ℝ) - 1 / 2
    (∫ t in Set.Ioi z, Real.exp (-s * t) * |P.eval t|) ≤
      Real.exp (-s * z) *
          (∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((k.factorial : ℝ) / s ^ (k + 1))) +
        2 * highNegativeMoment K j := by
  exact high_profile_abs_tail_le K h j (sub_pos.mpr (high_gaussian_pole_gt K)) hz

/-- An integer upper bound on the rounded sum gives a real upper bound
on the finite H28 correction integral. -/
public theorem high_negative_moment_le_of_ticks (K : HighGaussianKernel) {j : ℕ} {M : ℤ}
    (hM : highNegativeChargeTicks K j ≤ M) : highNegativeMoment K j ≤ (M : ℝ) / 10 ^ 6 := by
  refine (high_negative_moment_le K j).trans ?_
  have h :=
    (high_negative_charge_le_ticks K j).trans
      (div_le_div_of_nonneg_right (Int.cast_le.mpr hM) (by norm_num only))
  simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat] using
    (Rat.cast_le.mpr h : (highNegativeMomentCharge K j : ℝ) ≤ _)

/-- In the translated coordinate used by H29, the signed polynomial moment
has no exponential prefactor and the finite H28 charge is scaled by exp(s z). -/
public theorem high_shifted_moment_le (K : HighGaussianKernel)
    (h : highIntProfileSignCheck K (profileCorrectionEnd K) = true) (j : ℕ) {z : ℝ}
    (hz : (profileCorrectionStart K : ℝ) ≤ z) :
    let P := (Polynomial.derivative^[j]) K.realProfile
    let Q := P.comp (Polynomial.X + Polynomial.C z)
    let s := (K.pole : ℝ) - 1 / 2
    (∫ v in Set.Ioi (0 : ℝ), Real.exp (-s * v) * |P.eval (z + v)|) ≤
      (∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((k.factorial : ℝ) / s ^ (k + 1))) +
        2 * Real.exp (s * z) * highNegativeMoment K j := by
  intro P Q s
  have he :
    (∫ v in Set.Ioi (0 : ℝ), Real.exp (-s * v) * |P.eval (z + v)|) =
      Real.exp (s * z) * ∫ t in Set.Ioi z, Real.exp (-s * t) * |P.eval t| := by
    rw [← integral_translate_Ioi (fun t ↦ Real.exp (-s * t) * |P.eval t|) z, ←
      MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v _
    change
      Real.exp (-s * v) * |P.eval (z + v)| =
        Real.exp (s * z) * (Real.exp (-s * (z + v)) * |P.eval (z + v)|)
    rw [← mul_assoc, ← Real.exp_add, show s * z + -s * (z + v) = -s * v by ring]
  rw [he]
  have hm :=
    mul_le_mul_of_nonneg_left (high_abs_tail_le_negative K h j hz) (Real.exp_nonneg (s * z))
  have hx : Real.exp (s * z) * Real.exp (-s * z) = 1 := by
    rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
  simpa only [s, mul_add, ← mul_assoc, hx, one_mul, mul_comm (Real.exp (s * z)) 2] using hm

/-- The translated absolute Laplace moment is integrable at positive decay.
This permits splitting the H29 envelope into the two derivative moments. -/
public theorem integrable_shifted_abs_moment (P : Polynomial ℝ) (z : ℝ) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun v ↦ Real.exp (-s * v) * |P.eval (z + v)|) (Set.Ioi 0) := by
  have he (v : ℝ) : (P.comp (Polynomial.X + Polynomial.C z)).eval v = P.eval (z + v) := by
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, add_comm v]
  have hf :
    (fun v : ℝ ↦ Real.exp (-s * v) * |P.eval (z + v)|) = fun v ↦
      Real.exp (-s * v) * |(P.comp (Polynomial.X + Polynomial.C z)).eval v| :=
    funext fun v ↦ congrArg (fun x : ℝ ↦ Real.exp (-s * v) * |x|) (he v).symm
  rw [hf]
  exact (abs_laplace_integrable_and_le (P.comp (Polynomial.X + Polynomial.C z)) hs).1

/-- Bound the lower H27 integral by the three translated derivative moments.
The coefficients are the absolute values of those in the remainder polynomial. -/
public theorem high_remainder_moment_triangle (K : HighGaussianKernel) (z : ℝ) :
    let d := (K.pole : ℝ) - 1 / 2
    let B := K.realProfile
    let D :=
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative
    let M := fun P : Polynomial ℝ ↦ ∫ v in Set.Ioi (0 : ℝ), Real.exp (-d * v) * |P.eval (z + v)|
    M D ≤ d ^ 2 * M B + 2 * d * M B.derivative + M B.derivative.derivative := by
  intro d B D M
  let f := fun (P : Polynomial ℝ) (v : ℝ) ↦ Real.exp (-d * v) * |P.eval (z + v)|
  have hd : 0 < d := sub_pos.mpr (high_gaussian_pole_gt K)
  have hf (P : Polynomial ℝ) : MeasureTheory.IntegrableOn (f P) (Set.Ioi 0) :=
    integrable_shifted_abs_moment P z hd
  let g := fun v ↦ d ^ 2 * f B v + 2 * d * f B.derivative v + f B.derivative.derivative v
  have hg : MeasureTheory.IntegrableOn g (Set.Ioi 0) :=
    (((hf B).const_mul (d ^ 2)).add ((hf B.derivative).const_mul (2 * d))).add
      (hf B.derivative.derivative)
  have hpoint (v : ℝ) : f D v ≤ g v := by
    dsimp only [f, g, D]
    rw [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_C]
    have hsub (x y : ℝ) : |x - y| ≤ |x| + |y| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
    have h :=
      (abs_add_le (d ^ 2 * B.eval (z + v) - 2 * d * B.derivative.eval (z + v))
            (B.derivative.derivative.eval (z + v))).trans
        (add_le_add_left (hsub _ _) _)
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg d),
      abs_of_nonneg (mul_nonneg zero_le_two hd.le)] at h
    calc
      _ ≤
          Real.exp (-d * v) *
            (d ^ 2 * |B.eval (z + v)| + 2 * d * |B.derivative.eval (z + v)| +
              |B.derivative.derivative.eval (z + v)|) :=
        mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
      _ = _ := by ring
  calc
    M D ≤ ∫ v in Set.Ioi (0 : ℝ), g v :=
      MeasureTheory.setIntegral_mono_on (hf D) hg measurableSet_Ioi (fun v _ ↦ hpoint v)
    _ = _ := by
      dsimp only [g, M]
      change
        (∫ v in Set.Ioi (0 : ℝ),
            ((fun x ↦ d ^ 2 * f B x) + (fun x ↦ 2 * d * f B.derivative x)) v +
              f B.derivative.derivative v) =
          _
      rw [MeasureTheory.integral_add (((hf B).const_mul _).add ((hf B.derivative).const_mul _))
          (hf B.derivative.derivative)]
      simp only [Pi.add_apply]
      rw [MeasureTheory.integral_add ((hf B).const_mul _) ((hf B.derivative).const_mul _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

end PseudoPrime.PrimeTestBounds.MillerRabin
