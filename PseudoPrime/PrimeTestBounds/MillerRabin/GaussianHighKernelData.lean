/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Polynomial.BigOperators
public import PseudoPrime.LLS.PaperStatements.ShiftedPoleArithmetic
import Mathlib.Tactic.NormNum

/-! # Rational parameter data for the two high Gaussian kernels -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The two signed kernels used in the manuscript's high-range proof. -/
public inductive HighGaussianKernel
  | k186
  | k196

/-- The real location parameter of the kernel's negative pole. -/
@[expose]
public def HighGaussianKernel.pole : HighGaussianKernel → ℚ
  | .k186 => 11 / 4
  | .k196 => 13 / 4

/-- The degree parameter of the compact input polynomial. -/
@[expose]
public def HighGaussianKernel.degree : HighGaussianKernel → ℕ
  | .k186 => 40
  | .k196 => 56

private def coefficientTicks : HighGaussianKernel → List ℤ
  | .k186 =>
    [1000000000000, -9098262338414, 34386175178513, -68425063151298, 76106826672554,
      -49663116401988, 27066017006454, -19337660736189, 12138124330042, -11210909615431,
      8616982499734, -1533291674935, 4397016728521, -3462443977518, -372243767275, -2164330969955,
      668225205073, -150007566846, 693643760610, 55418648390, 598616962236, 434103799605,
      525056997602, 21203221958, -308917409674, -611206076838, -494155176576, -221015928425,
      148004894351, 344127726992, 359062813703, 199522691773, 10749752181, -120498290003,
      -134987510166, -61997372412, 41672646598, 116031611588, 128742032218, 94636661166,
      34135550507]
  | .k196 =>
    [1000000000000, -10515452268350, 47416964380864, -117282986002458, 172354912581650,
      -158476946829725, 107778983529549, -75124105512645, 49646924938032, -32792706884954,
      34893200149558, -23104371798280, 9889064659786, -13957236740135, 9168196266986,
      -4524939129896, 5315267034649, -2629219152774, 3383760012632, -960356828834, 1097620344494,
      -2191971217911, -766235639702, -1239917640893, 679661153796, 623409447553, 972651351249,
      60513211041, -193199557985, -521845005295, -179051287132, 29150508166, 275886611091,
      178063837659, 43955053510, -138873642696, -152198336294, -89086554524, 31570668842,
      71649334465, 27508200823, -94659218073, -202096577969, -240145776631, -173850451228,
      -39677051549, 105244724713, 192695191534, 191913110983, 105918522744, -22292520197,
      -144484014337, -215198698177, -223473552222, -173523099490, -102933283025, -32149456447]

private def tickGram (v : List ℤ) : ℤ :=
  (v.map fun x ↦ x * x).sum - (v.zipWith (· * ·) v.tail).sum

/-- The sum of the compact input coefficients, in units of one trillionth. -/
private theorem high_gaussian_tick_sum (K : HighGaussianKernel) :
    (coefficientTicks K).sum =
      match K with
      | .k186 => 813989428426
      | .k196 => -970498903459 := by
  cases K <;> decide +kernel

/-- The squared norm minus the sum of adjacent products is positive for both kernels. -/
private theorem tick_gram_pos (K : HighGaussianKernel) : 0 < tickGram (coefficientTicks K) := by
  cases K <;> decide +kernel

/-- The normalization multiplier from the manuscript's Gram formula.
The common fixed-point denominator cancels in the ratio. -/
public def HighGaussianKernel.normalization (K : HighGaussianKernel) : ℚ :=
  let v := coefficientTicks K
  3 * K.pole ^ 3 * (v.sum : ℚ) ^ 2 / (4 * (tickGram v : ℚ))

/-- The normalization multiplier of either high kernel is strictly positive. -/
public theorem high_gaussian_normalization_pos (K : HighGaussianKernel) : 0 < K.normalization := by
  cases K <;> decide +kernel

/-- The compact polynomial from (H3), written as a sum of products of
the monomials in the original and translated coordinates. -/
public noncomputable def HighGaussianKernel.polynomial (K : HighGaussianKernel) : Polynomial ℚ :=
  let v := coefficientTicks K
  ∑ j ∈ Finset.range (K.degree + 1),
    Polynomial.C (((v[j]?.getD 0 : ℤ) : ℚ) / (v.sum : ℚ)) * Polynomial.X ^ (K.degree - j) *
      (Polynomial.X - Polynomial.C (2 * K.pole)) ^ j

/-- The compact expression has degree at most the specified degree parameter. -/
public theorem high_gaussian_polynomial_degree (K : HighGaussianKernel) :
    K.polynomial.natDegree ≤ K.degree := by
  unfold HighGaussianKernel.polynomial
  dsimp only
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hj' : j ≤ K.degree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hleft :=
    Polynomial.natDegree_C_mul_X_pow_le
      (((((coefficientTicks K)[j]?).getD 0 : ℤ) : ℚ) / ((coefficientTicks K).sum : ℚ))
      (K.degree - j)
  have hright := Polynomial.natDegree_pow_le_of_le j (Polynomial.natDegree_X_sub_C_le (2 * K.pole))
  exact
    (Polynomial.natDegree_mul_le_of_le hleft hright).trans_eq
      (by rw [mul_one, Nat.sub_add_cancel hj'])

/-- The polynomial numerator coefficient in the partial-fraction expansion. -/
public noncomputable def HighGaussianKernel.expandedCoeff (K : HighGaussianKernel) (j : ℕ) : ℚ :=
  K.normalization * (K.polynomial ^ 2).coeff j

/-- The coefficient of the compact numerator is a finite rational binomial sum. -/
private def compactCoeff (K : HighGaussianKernel) (i : ℕ) : ℚ :=
  let v := coefficientTicks K
  ∑ j ∈ Finset.range (K.degree + 1),
    ((v[j]?.getD 0 : ℤ) : ℚ) / (v.sum : ℚ) *
      if K.degree - j ≤ i then
        (-(2 * K.pole)) ^ (j - (i - (K.degree - j))) * (j.choose (i - (K.degree - j)) : ℚ)
      else 0

/-- The rational sum computes the original numerator coefficient. -/
private theorem compact_coeff_eq (K : HighGaussianKernel) (i : ℕ) :
    K.polynomial.coeff i = compactCoeff K i := by
  simp only [HighGaussianKernel.polynomial, compactCoeff, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', sub_eq_add_neg, ←
    Polynomial.C_neg, Polynomial.coeff_X_add_C_pow]

/-- Compute the normalized square numerator coefficient by convolution of
the rational compact coefficients, without constructing a polynomial. -/
public def HighGaussianKernel.expandedCoeffRat (K : HighGaussianKernel) (j : ℕ) : ℚ :=
  K.normalization * ∑ ij ∈ Finset.antidiagonal j, compactCoeff K ij.1 * compactCoeff K ij.2

/-- Compute the entire normalized square numerator with a shared compact coefficient table. -/
public def HighGaussianKernel.expandedCoeffRow (K : HighGaussianKernel) : Array ℚ :=
  let c := Array.ofFn (fun i : Fin (2 * K.degree + 1) ↦ compactCoeff K i.val)
  Array.ofFn
    (fun j : Fin (2 * K.degree + 1) ↦
      K.normalization * ∑ ij ∈ Finset.antidiagonal j.val, c[ij.1]?.getD 0 * c[ij.2]?.getD 0)

/-- Lookup of an in-range entry gives the normalized rational convolution coefficient. -/
public theorem high_expanded_row_get (K : HighGaussianKernel) {j : ℕ} (hj : j < 2 * K.degree + 1) :
    K.expandedCoeffRow[j]?.getD 0 = K.expandedCoeffRat j := by
  simp only [HighGaussianKernel.expandedCoeffRow, HighGaussianKernel.expandedCoeffRat, getElem?_def,
    Array.size_ofFn, hj, dite_eq_left, Array.getElem_ofFn, Option.getD_some]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  have h := Finset.mem_antidiagonal.mp hij
  have h1 := (Nat.le_add_right ij.1 ij.2).trans_lt (h ▸ hj)
  have h2 := (Nat.le_add_left ij.2 ij.1).trans_lt (h ▸ hj)
  simp only [h1, h2, dite_eq_left, Option.getD_some]

/-- The rational convolution agrees with the numerator coefficient used by
the analytic high-kernel development. -/
public theorem high_expanded_coeff_rat (K : HighGaussianKernel) (j : ℕ) :
    K.expandedCoeff j = K.expandedCoeffRat j := by
  simp only [HighGaussianKernel.expandedCoeff, HighGaussianKernel.expandedCoeffRat, pow_two,
    Polynomial.coeff_mul, compact_coeff_eq]

/-- Compute one compact coefficient so numerical certificates can validate
the compact inputs before performing the normalized square convolution. -/
public def HighGaussianKernel.compactCoeffAt (K : HighGaussianKernel) (i : ℕ) : ℚ :=
  compactCoeff K i

/-- Terms above twice the compact degree have zero numerator coefficient. -/
public theorem high_gaussian_coeff_zero (K : HighGaussianKernel) {j : ℕ} (hj : 2 * K.degree < j) :
    K.expandedCoeff j = 0 := by
  have hd := (Polynomial.natDegree_pow_le_of_le 2 (high_gaussian_polynomial_degree K)).trans_lt hj
  rw [HighGaussianKernel.expandedCoeff, Polynomial.coeff_eq_zero_of_natDegree_lt hd, mul_zero]

/-- The logarithmic monomial exponent for an expanded numerator term.
The corresponding shifted pole has order one higher. -/
@[expose]
public def HighGaussianKernel.logPower (K : HighGaussianKernel) (j : ℕ) : ℕ :=
  2 * K.degree - j + 3

/-- Each component has a shifted pole of order at least four. -/
public theorem high_gaussian_order_ge_four (K : HighGaussianKernel) (j : ℕ) :
    4 ≤ K.logPower j + 1 := by exact Nat.le_add_left 4 _

/-- Both high-kernel poles lie strictly to the left of the critical strip. -/
public theorem high_gaussian_pole_gt (K : HighGaussianKernel) : (1 / 2 : ℝ) < K.pole := by
  cases K <;> norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]

/-- The real argument of the physical polynomial is the reversed logarithmic
coordinate, with the manuscript's normalization already included. -/
public noncomputable def HighGaussianKernel.profilePoly (K : HighGaussianKernel) (z : ℝ) : ℂ :=
  LLS.PaperStatements.shiftedPolePolynomial (Finset.range (2 * K.degree + 1)) K.logPower
    (fun j ↦ (K.expandedCoeff j : ℂ)) z

/-- The shift-five arithmetic series for each high kernel is exactly the
finite Mangoldt sum with its specified polynomial. -/
public theorem high_gaussian_arithmetic (K : HighGaussianKernel) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ,
        ∑ j ∈ Finset.range (2 * K.degree + 1),
          (K.expandedCoeff j : ℂ) *
            (LLS.PaperStatements.shiftedPoleKernel (K.logPower j) K.pole 5
                  ((by decide : 1 ≤ 3).trans (Nat.le_add_left _ _))
                  (high_gaussian_pole_gt K)).summand
              χ x n) =
      ∑ n ∈ Finset.Ioc 0 ⌊x * Real.exp 5⌋₊,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
          (((((n : ℝ) / x) * Real.exp (-5)) ^ (K.pole : ℝ) : ℝ) : ℂ) *
          K.profilePoly (5 - Real.log ((n : ℝ) / x)) := by
  exact
    LLS.PaperStatements.shiftedPole_summand_tsum (Finset.range (2 * K.degree + 1)) K.logPower
      (fun j ↦ (K.expandedCoeff j : ℂ)) (fun _ ↦ (by decide : 1 ≤ 3).trans (Nat.le_add_left _ _))
      (high_gaussian_pole_gt K) hx χ

end PseudoPrime.PrimeTestBounds.MillerRabin
