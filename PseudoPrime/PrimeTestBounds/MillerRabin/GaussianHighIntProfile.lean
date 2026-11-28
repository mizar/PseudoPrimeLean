/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensation
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntRow

/-! # Denominator-cleared integer profiles for the high Gaussian kernels -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Return the integer numerator of the pole over four. -/
private def poleQuarter (K : HighGaussianKernel) : ℤ :=
  match K with
  | .k186 => 11
  | .k196 => 13

/-- The integer pole numerator represents the analytic pole exactly. -/
private theorem pole_eq (K : HighGaussianKernel) : K.pole = (poleQuarter K : ℚ) / 4 := by
  cases K <;> rfl

/-- Clear a power of the half-integer pole using a common binary denominator. -/
private theorem cleared_power (p : ℤ) (d j : ℕ) (hj : j ≤ d) :
    (((-p) ^ j * 2 ^ (d - j) : ℤ) : ℚ) / 2 ^ d = (-(p : ℚ) / 2) ^ j := by
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_ofNat, div_pow]
  calc
    _ = (-(p : ℚ)) ^ j * 2 ^ (d - j) / (2 ^ j * 2 ^ (d - j)) := by
      rw [← pow_add, Nat.add_sub_of_le hj]
    _ = _ := mul_div_mul_right _ _ (pow_ne_zero _ (by norm_num only))

/-- Compute a compact coefficient from integer ticks before division by the common scale. -/
private def scaledCompact (K : HighGaussianKernel) (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (K.degree + 1),
    if K.degree - j ≤ i then
      let k := i - (K.degree - j)
      let e := j - k
      (coefficientTicks K)[j]?.getD 0 * ((-poleQuarter K) ^ e * 2 ^ (K.degree - e)) *
        (Nat.fast_choose j k : ℤ)
    else 0

/-- Dividing by the common scale recovers the rational compact coefficient. -/
private theorem scaled_compact_eq (K : HighGaussianKernel) (i : ℕ) :
    (scaledCompact K i : ℚ) / ((coefficientTicks K).sum * 2 ^ K.degree : ℚ) =
      K.compactCoeffAt i := by
  simp only [scaledCompact, HighGaussianKernel.compactCoeffAt, compactCoeff, Int.cast_sum,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : K.degree - j ≤ i
  · let k := i - (K.degree - j)
    let e := j - k
    have he : e ≤ K.degree := (Nat.sub_le j k).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    have hp : -(2 * K.pole) = -(poleQuarter K : ℚ) / 2 := by
      rw [pole_eq]; ring
    simp only [ite_eq_left h, Int.cast_mul, Int.cast_natCast, ← Nat.choose_eq_fast_choose, hp]
    rw [← div_mul_div_comm]
    rw [← cleared_power (poleQuarter K) K.degree e he]
    simp only [Int.cast_mul]
    ring
  · simp only [ite_eq_right h, Int.cast_zero, zero_div, mul_zero]

/-- Convolve two denominator-cleared compact coefficient rows. -/
private def scaledSquare (K : HighGaussianKernel) (j : ℕ) : ℤ :=
  ∑ ij ∈ Finset.antidiagonal j, scaledCompact K ij.1 * scaledCompact K ij.2

/-- Cancel the squared tick sum against the kernel's normalization. -/
private theorem normalized_square (p V T C : ℚ) (d : ℕ) (hV : V ≠ 0) (hT : T ≠ 0) :
    (3 * (p / 4) ^ 3 * V ^ 2 / (4 * T)) * (C / (V * 2 ^ d) ^ 2) =
      3 * p ^ 3 * C / (T * 2 ^ (2 * d + 8)) := by
  have hp : (2 : ℚ) ^ (2 * d + 8) = 256 * ((2 : ℚ) ^ d) ^ 2 := by
    rw [pow_add, mul_comm 2 d, pow_mul]
    norm_num only
    ring
  rw [hp]
  field_simp [hV, hT]
  ring

/-- The integer convolution gives the normalized rational square coefficient. -/
private theorem scaled_square_eq (K : HighGaussianKernel) (j : ℕ) :
    K.expandedCoeffRat j =
      ((3 * (poleQuarter K) ^ 3 * scaledSquare K j : ℤ) : ℚ) /
        ((tickGram (coefficientTicks K) : ℚ) * 2 ^ (2 * K.degree + 8)) := by
  let V : ℚ := ((coefficientTicks K).sum : ℤ)
  have hV : V ≠ 0 := by cases K <;> decide +kernel
  have hT : (tickGram (coefficientTicks K) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (tick_gram_pos K).ne'
  have hs :
    (∑ ij ∈ Finset.antidiagonal j, compactCoeff K ij.1 * compactCoeff K ij.2) =
      (scaledSquare K j : ℚ) / (V * 2 ^ K.degree) ^ 2 := by
    simp only [scaledSquare, Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ij _
    rw [pow_two, Int.cast_mul, ← div_mul_div_comm]
    exact congrArg₂ (· * ·) (scaled_compact_eq K ij.1).symm (scaled_compact_eq K ij.2).symm
  simp only [HighGaussianKernel.expandedCoeffRat, HighGaussianKernel.normalization, pole_eq, hs,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  exact normalized_square (poleQuarter K : ℚ) V _ (scaledSquare K j : ℚ) _ hV hT

/-- Return the physical profile's degree bound. -/
private def profileDegree (K : HighGaussianKernel) : ℕ :=
  2 * K.degree + 3

/-- Use the Gram difference, binary scale and top factorial as a positive common denominator. -/
private def profileDen (K : HighGaussianKernel) : ℤ :=
  tickGram (coefficientTicks K) * 2 ^ (profileDegree K + 5) * (profileDegree K).factorial

/-- Specify a numerator using the reversed square coefficient and the factorial ratio. -/
private def profileNum (K : HighGaussianKernel) (k : ℕ) : ℤ :=
  if 3 ≤ k then
    3 * poleQuarter K ^ 3 * scaledSquare K (profileDegree K - k) *
      ((profileDegree K).factorial / k.factorial : ℕ)
  else 0

/-- The factorial ratio is an exact integer when the coefficient index is in range. -/
private theorem factorial_ratio_cast {n k : ℕ} (hk : k ≤ n) :
    ((n.factorial / k.factorial : ℕ) : ℚ) = (n.factorial : ℚ) / k.factorial := by
  apply (eq_div_iff (Nat.cast_ne_zero.mpr k.factorial_ne_zero)).mpr
  exact_mod_cast Nat.div_mul_cancel (Nat.factorial_dvd_factorial hk)

/-- The physical profile reverses the expanded indices starting from degree three. -/
private theorem square_to_profile_index (d k : ℕ) (hk : 3 ≤ k) :
    2 * d + 3 - k = 2 * d - (k - 3) := by
  calc
    _ = 2 * d + 3 - (3 + (k - 3)) := by rw [Nat.add_sub_of_le hk]
    _ = _ := by rw [← Nat.sub_sub, Nat.add_sub_cancel]

/-- Each physical coefficient is supplied by its unique log-power term. -/
private theorem physical_coefficient (K : HighGaussianKernel) {k : ℕ} (hk : k ≤ 2 * K.degree + 3) :
    K.ratProfile.coeff k =
      if 3 ≤ k then K.expandedCoeffRat (2 * K.degree - (k - 3)) / (k.factorial : ℚ) else 0 := by
  rw [high_rat_profile_coeff, HighGaussianKernel.ratProfileCoeff]
  by_cases h : 3 ≤ k
  · rw [ite_eq_left h]
    let j := 2 * K.degree - (k - 3)
    have hk' : k - 3 ≤ 2 * K.degree := by
      simpa only [Nat.add_sub_cancel] using Nat.sub_le_sub_right hk 3
    have hj : j ∈ Finset.range (2 * K.degree + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _))
    have he : K.logPower j = k := by
      dsimp only [j]
      rw [HighGaussianKernel.logPower, Nat.sub_sub_self hk', Nat.sub_add_cancel h]
    rw [Finset.sum_eq_single_of_mem j hj]
    · rw [ite_eq_left he, he]
    · intro i hi hne
      have hle := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hn : K.logPower i ≠ k := by
        intro hh
        apply hne
        have ht := congrArg (fun n : ℕ ↦ 2 * K.degree - (n - 3)) hh
        simpa only [HighGaussianKernel.logPower, Nat.add_sub_cancel, Nat.sub_sub_self hle] using ht
      exact ite_eq_right hn
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro j hj
    have hl : 3 ≤ K.logPower j := Nat.le_add_left _ _
    exact ite_eq_right (fun he : K.logPower j = k ↦ h (he ▸ hl))

/-- Dividing the profile numerator by the common denominator gives the analytic coefficient. -/
private theorem profile_num_eq (K : HighGaussianKernel) {k : ℕ} (hk : k ≤ profileDegree K) :
    (profileNum K k : ℚ) / profileDen K = K.ratProfile.coeff k := by
  rw [physical_coefficient K hk]
  by_cases h : 3 ≤ k
  · simp only [profileNum, profileDen, ite_eq_left h, scaled_square_eq, Int.cast_mul, Int.cast_pow,
      Int.cast_ofNat, Int.cast_natCast, factorial_ratio_cast hk]
    rw [show profileDegree K - k = 2 * K.degree - (k - 3) from square_to_profile_index K.degree k h]
    have hF : ((profileDegree K).factorial : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (profileDegree K).factorial_ne_zero
    change _ / (_ * (2 : ℚ) ^ (2 * K.degree + 8) * _) = _
    rw [← mul_div_assoc, div_div]
    rw [show
        (k.factorial : ℚ) *
            ((tickGram (coefficientTicks K) : ℚ) * 2 ^ (2 * K.degree + 8) *
              (profileDegree K).factorial) =
          ((tickGram (coefficientTicks K) : ℚ) * 2 ^ (2 * K.degree + 8) * k.factorial) *
            (profileDegree K).factorial
        by ring]
    simpa only [div_div] using mul_div_mul_right _ _ hF
  · simp only [profileNum, ite_eq_right h, Int.cast_zero, zero_div]

/-- The last m products of the square convolution repeat the first m in reverse order. -/
private theorem square_tail_eq (f : ℕ → ℤ) (j a m : ℕ) (h : j + 1 = a + m) :
    (∑ i ∈ Finset.range m, f (a + i) * f (j - (a + i))) =
      ∑ i ∈ Finset.range m, f i * f (j - i) := by
  rw [← Finset.sum_range_reflect (fun i ↦ f i * f (j - i)) m]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
  have hle : a + i ≤ j := by
    apply Nat.le_of_succ_le_succ
    change a + i + 1 ≤ j + 1
    rw [h, Nat.add_assoc]
    exact Nat.add_le_add_left hi' a
  have hidx : j - (a + i) = m - 1 - i := by
    rw [← Nat.succ_sub_succ_eq_sub]
    change j + 1 - (a + i + 1) = _
    rw [h, Nat.add_assoc, Nat.add_sub_add_left, Nat.sub_sub, Nat.add_comm i 1]
  rw [← hidx, Nat.sub_sub_self hle, mul_comm]

/-- Compute one square coefficient using a single product per symmetric pair. -/
private def squareByPairs (f : ℕ → ℤ) (j : ℕ) : ℤ :=
  let m := j / 2
  if j % 2 = 0 then 2 * (∑ i ∈ Finset.range m, f i * f (j - i)) + f m ^ 2
  else 2 * (∑ i ∈ Finset.range (m + 1), f i * f (j - i))

/-- The symmetric-pair formula equals the usual ordered convolution. -/
private theorem square_by_pairs_eq (f : ℕ → ℤ) (j : ℕ) :
    squareByPairs f j = ∑ ij ∈ Finset.antidiagonal j, f ij.1 * f ij.2 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i l ↦ f i * f l) j, squareByPairs]
  change _ = ∑ i ∈ Finset.range (j + 1), f i * f (j - i)
  let m := j / 2
  have hj : j % 2 + (m + m) = j := by simpa only [Nat.two_mul] using Nat.mod_add_div j 2
  rcases Nat.mod_two_eq_zero_or_one j with hz | ho
  · have hv : m + m = j := by simpa only [hz, Nat.zero_add] using hj
    have h : j + 1 = (m + 1) + m := by rw [← hv, Nat.add_right_comm]
    have hd : j - m = m := by rw [← hv, Nat.add_sub_cancel]
    rw [ite_eq_left hz, h, Finset.sum_range_add, square_tail_eq f j (m + 1) m h,
      Finset.sum_range_succ, hd, pow_two]
    ring
  · have h : j + 1 = (m + 1) + (m + 1) := by
      rw [← hj, ho]
      ac_rfl
    rw [ite_eq_right (ho.trans_ne (by decide)), h,
      Finset.sum_range_add (fun i ↦ f i * f (j - i)) (m + 1) (m + 1),
      square_tail_eq f j (m + 1) (m + 1) h, two_mul]

/-- Build the integer convolution using a shared compact row. -/
private def squareRow (K : HighGaussianKernel) : Array ℤ :=
  let compact := Array.ofFn (fun i : Fin (2 * K.degree + 1) ↦ scaledCompact K i.val)
  Array.ofFn fun j : Fin (2 * K.degree + 1) ↦ squareByPairs (fun i ↦ compact[i]?.getD 0) j.val

/-- An in-range convolution entry agrees with the scalar specification. -/
private theorem square_row_get (K : HighGaussianKernel) {j : ℕ} (hj : j < 2 * K.degree + 1) :
    (squareRow K)[j]?.getD 0 = scaledSquare K j := by
  simp only [squareRow, scaledSquare, Array.getElem?_ofFn, dite_eq_left hj, Option.getD_some,
    square_by_pairs_eq]
  apply Finset.sum_congr rfl
  intro ij hij
  have h := Finset.mem_antidiagonal.mp hij
  have h1 := (Nat.le_add_right ij.1 ij.2).trans_lt (h ▸ hj)
  have h2 := (Nat.le_add_left ij.2 ij.1).trans_lt (h ▸ hj)
  simp only [h1, h2, dite_eq_left, Option.getD_some]

/-- Generate descending factorial ratios, starting with the supplied top value. -/
private def factorialRatioList : ℕ → ℕ → List ℕ
  | 0, r => [r]
  | n + 1, r => r :: factorialRatioList n (r * (n + 1))

/-- The entry at offset j multiplies the top value by the first j descending factors. -/
private theorem factorial_ratio_list_get (n r j : ℕ) (hj : j ≤ n) :
    (factorialRatioList n r)[j]?.getD 0 = r * n.descFactorial j := by
  induction n generalizing r j with
  | zero =>
    have he := Nat.eq_zero_of_le_zero hj
    subst j
    simp only [factorialRatioList, List.getElem?_cons_zero, Option.getD_some,
      Nat.descFactorial_zero, Nat.mul_one]
  | succ n ih =>
    cases j with
    | zero =>
      simp only [factorialRatioList, List.getElem?_cons_zero, Option.getD_some,
        Nat.descFactorial_zero, Nat.mul_one]
    | succ j =>
      simp only [factorialRatioList, List.getElem?_cons_succ,
        ih (r * (n + 1)) j (Nat.le_of_succ_le_succ hj), Nat.succ_descFactorial_succ, Nat.mul_assoc]

/-- Read a shared array of exact ratios N! / k! at offset N-k. -/
private theorem factorial_ratio_array_get (N k : ℕ) (hk : k ≤ N) :
    ((factorialRatioList N 1).toArray)[N - k]?.getD 0 = N.factorial / k.factorial := by
  rw [List.getElem?_toArray, factorial_ratio_list_get N 1 _ (Nat.sub_le _ _), Nat.one_mul,
    Nat.descFactorial_eq_div (Nat.sub_le N k), Nat.sub_sub_self hk]

/-- Generate a denominator-cleared physical profile for either high Gaussian kernel.
The compact coefficients and their convolution are computed entirely with integers. -/
public def highProfileIntRow (K : HighGaussianKernel) : MiddleIntRow :=
  let N := profileDegree K
  let C := squareRow K
  let F := (factorialRatioList N 1).toArray
  ⟨profileDen K,
    Array.ofFn fun k : Fin (N + 1) ↦
      if 3 ≤ k.val then 3 * poleQuarter K ^ 3 * C[N - k.val]?.getD 0 * (F[N - k.val]?.getD 0 : ℕ)
      else 0⟩

/-- Lookup of a generated physical numerator agrees with its coefficient specification. -/
private theorem profile_row_num (K : HighGaussianKernel) {k : ℕ} (hk : k ≤ profileDegree K) :
    (highProfileIntRow K).num k = profileNum K k := by
  have hi : k < profileDegree K + 1 := Nat.lt_succ_of_le hk
  by_cases h : 3 ≤ k
  · have hj : profileDegree K - k < 2 * K.degree + 1 := by
      rw [profileDegree, square_to_profile_index K.degree k h]
      exact Nat.lt_succ_of_le (Nat.sub_le _ _)
    simp only [highProfileIntRow, MiddleIntRow.num, Array.getElem?_ofFn, dite_eq_left hi,
      Option.getD_some, ite_eq_left h, square_row_get K hj, factorial_ratio_array_get _ _ hk,
      profileNum]
  · simp only [highProfileIntRow, MiddleIntRow.num, Array.getElem?_ofFn, dite_eq_left hi,
      Option.getD_some, ite_eq_right h, profileNum]

/-- The generated row represents the original physical polynomial coefficient by coefficient. -/
public theorem high_profile_int_poly (K : HighGaussianKernel) :
    (highProfileIntRow K).poly (2 * K.degree + 3) = K.ratProfile := by
  change (highProfileIntRow K).poly (profileDegree K) = K.ratProfile
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro k
  by_cases hk : k ≤ profileDegree K
  · rw [MiddleIntRow.poly_coeff _ hk, profile_row_num K hk]
    exact profile_num_eq K hk
  · have hd := Nat.lt_of_not_ge hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt _,
      Polynomial.coeff_eq_zero_of_natDegree_lt ((high_rat_profile_degree K).trans_lt hd)]
    exact (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos _) _)).trans_lt hd

/-- The common denominator is positive for either high kernel. -/
public theorem high_profile_int_den_pos (K : HighGaussianKernel) :
    0 < (highProfileIntRow K).den := by
  exact
    mul_pos (mul_pos (tick_gram_pos K) (pow_pos (by decide) _))
      (Int.ofNat_lt.mpr (Nat.factorial_pos _))

/-- The generated row has one entry for each supported physical degree. -/
public theorem high_profile_int_size (K : HighGaussianKernel) :
    (highProfileIntRow K).nums.size = 2 * K.degree + 4 := by
  simp only [highProfileIntRow, Array.size_ofFn, profileDegree]

end PseudoPrime.PrimeTestBounds.MillerRabin
