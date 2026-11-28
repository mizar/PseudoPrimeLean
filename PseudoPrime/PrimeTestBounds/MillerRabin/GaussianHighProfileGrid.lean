/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighProfileSign
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighProfileSign
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData

/-! # Shared integer profile calculations for the high Gaussian kernels -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A common denominator for the shifted profile row. -/
private def highGammaProfileDen (m : ℕ) (B : Array ℚ) : ℕ :=
  (Finset.range m).lcm fun i ↦ (B[i]?.getD 0).den

/-- Scale each shifted profile coefficient by the shared denominator. -/
private def highGammaProfileInt (m : ℕ) (B : Array ℚ) : Array ℤ :=
  let H := highGammaProfileDen m B
  Array.ofFn fun i : Fin m ↦ clearedProfileCoeff H (B[i.val]?.getD 0)

/-- Integer clearing preserves each coefficient after rescaling. -/
private theorem high_gamma_profile_int_cast (m : ℕ) (B : Array ℚ) {i : ℕ} (hi : i < m) :
    ((highGammaProfileInt m B)[i]?.getD 0 : ℚ) = (highGammaProfileDen m B : ℚ) * B[i]?.getD 0 := by
  have h : (B[i]?.getD 0).den ∣ highGammaProfileDen m B := Finset.dvd_lcm (Finset.mem_range.mpr hi)
  simpa only [highGammaProfileInt, Array.getElem?_ofFn, dite_eq_left hi, Option.getD_some] using
    cleared_profile_coeff_cast (highGammaProfileDen m B) (B[i]?.getD 0) h

/-- The common denominator is positive, since every rational denominator is positive. -/
private theorem high_gamma_profile_den_pos (m : ℕ) (B : Array ℚ) : 0 < highGammaProfileDen m B := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr (fun i _ ↦ (B[i]?.getD 0).den_ne_zero)

/-- One integer shift coefficient, using a precomputed grid of powers. -/
private def highGammaShiftCoeff (m : ℕ) (b powers : Array ℤ) (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range m, b[j]?.getD 0 * ((Nat.fast_choose j i : ℤ) * powers[j - i]?.getD 0)

/-- Shift a denominator-cleared power row to an integer origin.
The powers of the origin are shared by all output coefficients. -/
private def highGammaShiftInt (m : ℕ) (a : ℤ) (b : Array ℤ) : Array ℤ :=
  let powers := Array.ofFn fun j : Fin m ↦ a ^ j.val
  Array.ofFn fun i : Fin m ↦ highGammaShiftCoeff m b powers i.val

/-- Integer translation of cleared coefficients agrees with affine
composition of the corresponding rational polynomial. -/
private theorem high_gamma_shift_int_cast (m : ℕ) (a : ℤ) (b : Array ℤ) (H : ℕ) (P : Polynomial ℚ)
    (hd : P.natDegree + 1 ≤ m) (hb : ∀ j < m, (b[j]?.getD 0 : ℚ) = (H : ℚ) * P.coeff j) {i : ℕ}
    (hi : i < m) :
    ((highGammaShiftInt m a b)[i]?.getD 0 : ℚ) =
      (H : ℚ) * (P.comp (Polynomial.X + Polynomial.C (a : ℚ))).coeff i := by
  have hm : P.natDegree ≤ m - 1 := Nat.le_sub_of_add_le hd
  have hms : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.one_le_of_lt hi)
  have h := Analysis.rational_affine_coeff P (m - 1) hm (a : ℚ) 1 i
  simp only [hms, Polynomial.C_1, one_mul, one_pow] at h
  rw [h, Finset.mul_sum]
  simp only [highGammaShiftInt, highGammaShiftCoeff, Array.getElem?_ofFn, dite_eq_left hi,
    Option.getD_some, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hji := (Nat.sub_le j i).trans_lt hj'
  simp only [dite_eq_left hji, Option.getD_some, Int.cast_pow, hb j hj', mul_assoc]

/-- Read the unique expanded term contributing to one profile coefficient. -/
private def highGammaBaseAt (degree : ℕ) (numerator : Array ℚ) (k : ℕ) : ℚ :=
  if 3 ≤ k then numerator[2 * degree - (k - 3)]?.getD 0 / (k.factorial : ℚ) else 0

/-- Assemble the unshifted power row from the normalized expanded numerator. -/
private def highGammaBaseFrom (degree : ℕ) (numerator : Array ℚ) : Array ℚ :=
  Array.ofFn (fun k : Fin (2 * degree + 4) ↦ highGammaBaseAt degree numerator k.val)

/-- Each term of the unshifted profile can be recovered with one lookup. -/
private theorem high_gamma_direct_base_coeff (K : HighGaussianKernel) {i : ℕ}
    (hi : i < 2 * K.degree + 4) :
    (highGammaBaseFrom K.degree K.expandedCoeffRow)[i]?.getD 0 = K.ratProfile.coeff i := by
  simp only [highGammaBaseFrom, highGammaBaseAt, Array.getElem?_ofFn, dite_eq_left hi,
    Option.getD_some, high_rat_profile_coeff, HighGaussianKernel.ratProfileCoeff]
  by_cases h3 : 3 ≤ i
  · rw [ite_eq_left h3]
    let j := 2 * K.degree - (i - 3)
    have hj : j < 2 * K.degree + 1 := Nat.lt_succ_of_le (Nat.sub_le _ _)
    have hi' : i - 3 ≤ 2 * K.degree := by
      simpa only [Nat.add_sub_cancel] using Nat.sub_le_sub_right (Nat.le_of_lt_succ hi) 3
    have hj' : K.logPower j = i := by
      simp only [HighGaussianKernel.logPower, j, Nat.sub_sub_self hi', Nat.sub_add_cancel h3]
    rw [high_expanded_row_get K hj, Finset.sum_eq_single j]
    · rw [ite_eq_left hj', hj']
    · intro k hk hne
      apply ite_eq_right
      intro he
      apply hne
      have hk' := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have h := congrArg (fun n : ℕ ↦ 2 * K.degree - (n - 3)) he
      simpa only [HighGaussianKernel.logPower, Nat.add_sub_cancel, Nat.sub_sub_self hk', j] using h
    · intro hn
      exact (hn (Finset.mem_range.mpr hj)).elim
  · rw [ite_eq_right h3, Finset.sum_eq_zero]
    intro j _
    apply ite_eq_right
    intro h
    exact h3 (h ▸ Nat.le_add_left 3 _)

/-- Build the unshifted profile row from the normalized expanded numerator. -/
private def highGammaBaseRow (K : HighGaussianKernel) : Array ℚ :=
  highGammaBaseFrom K.degree K.expandedCoeffRow

/-- Clear the denominator before translating, so all shift sums are integral. -/
private def highGammaShiftedProfile (K : HighGaussianKernel) (a : ℤ) : Array ℤ :=
  let m := 2 * K.degree + 4
  highGammaShiftInt m a (highGammaProfileInt m (highGammaBaseRow K))

/-- The computed shifted row is scaled by the unshifted common denominator. -/
private theorem high_gamma_shifted_cast (K : HighGaussianKernel) (a : ℤ) {i : ℕ}
    (hi : i < 2 * K.degree + 4) :
    ((highGammaShiftedProfile K a)[i]?.getD 0 : ℚ) =
      (highGammaProfileDen (2 * K.degree + 4) (highGammaBaseRow K) : ℚ) *
        (K.cellPowerRow (a : ℚ) 1)[i]?.getD 0 := by
  have hd := Nat.succ_le_succ (high_rat_profile_degree K)
  have h :=
    high_gamma_shift_int_cast (2 * K.degree + 4) a
      (highGammaProfileInt (2 * K.degree + 4) (highGammaBaseRow K))
      (highGammaProfileDen (2 * K.degree + 4) (highGammaBaseRow K)) K.ratProfile hd
      (fun j hj ↦ by
        rw [high_gamma_profile_int_cast _ _ hj]
        exact
          congrArg ((highGammaProfileDen (2 * K.degree + 4) (highGammaBaseRow K) : ℚ) * ·)
            (high_gamma_direct_base_coeff K hj))
      hi
  rw [high_cell_power_coeff K (a : ℚ) 1 hi, Polynomial.C_1, one_mul]
  exact h

/-- Reuse verified expanded and shifted rows without redoing an earlier stage. -/
private theorem high_gamma_profile_of_stages (K : HighGaussianKernel) (a : ℤ) {e : Array ℚ}
    {base shifted : Array ℤ} (he : K.expandedCoeffRow = e)
    (hb : highGammaProfileInt (2 * K.degree + 4) (highGammaBaseFrom K.degree e) = base)
    (hs : highGammaShiftInt (2 * K.degree + 4) a base = shifted) :
    highGammaShiftedProfile K a = shifted := by
  simpa only [highGammaShiftedProfile, highGammaBaseRow, he, hb] using hs

/-- Compare a finite block of scalar computations with a literal certificate. -/
private def highGammaScalarEqBlock {α : Type} [DecidableEq α] (m : ℕ) (f : ℕ → α) (b : Array α)
    (start count : ℕ) : Bool :=
  (List.range count).all fun k ↦
    let i := start + k
    decide ((if i < m then some (f i) else none) = b[i]?)

/-- Scalar checks certify the generated array without evaluating the array itself. -/
private theorem high_gamma_row_of_scalar_blocks {α : Type} [DecidableEq α] (m : ℕ) (f : ℕ → α)
    (b : Array α) {width : ℕ} (hw : 0 < width) (hs : m = b.size)
    (h : ∀ k, width * k < m → highGammaScalarEqBlock m f b (width * k) width = true) :
    (Array.ofFn (fun i : Fin m ↦ f i.val)) = b := by
  apply Array.ext (Array.size_ofFn.trans hs)
  intro i hai hbi
  have hi : i < m := by simpa only [Array.size_ofFn] using hai
  have hk := (Nat.mul_div_le i width).trans_lt hi
  have he :=
    of_decide_eq_true
      (List.all_eq_true.mp (h (i / width) hk) (i % width) (List.mem_range.mpr (Nat.mod_lt i hw)))
  rw [Nat.add_comm, Nat.mod_add_div, ite_eq_left hi, Array.getElem?_eq_getElem hbi] at he
  simpa only [Array.getElem_ofFn] using Option.some.inj he

/-- Factor the common pole power and denominator out of the compact row sum. -/
private def highCompactFactored (K : HighGaussianKernel) (i : ℕ) : ℚ :=
  if i ≤ K.degree then
    let v := coefficientTicks K
    let k := K.degree - i
    (-(2 * K.pole)) ^ k / (v.sum : ℚ) *
      (↑(∑ j ∈ Finset.range (K.degree + 1), v[j]?.getD 0 * (Nat.fast_choose j k : ℤ)) : ℚ)
  else 0

/-- The factored integer sum recovers the original compact coefficient. -/
private theorem high_compact_factored_eq (K : HighGaussianKernel) (i : ℕ) :
    highCompactFactored K i = compactCoeff K i := by
  by_cases hi : i ≤ K.degree
  · simp only [highCompactFactored, ite_eq_left hi, compactCoeff, Int.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    by_cases h : K.degree - j ≤ i
    · have he : (K.degree - i) + (i - (K.degree - j)) = j := by
        rw [← Nat.add_sub_assoc h, Nat.sub_add_cancel hi, Nat.sub_sub_self hj']
      have hpow : j - (i - (K.degree - j)) = K.degree - i := by
        calc
          _ = (K.degree - i + (i - (K.degree - j))) - (i - (K.degree - j)) :=
            congrArg (· - (i - (K.degree - j))) he.symm
          _ = _ := Nat.add_sub_cancel _ _
      rw [ite_eq_left h, hpow, ← Nat.choose_symm_of_eq_add he.symm]
      simp only [Int.cast_mul, Int.cast_natCast, Nat.choose_eq_fast_choose]
      ring
    · have hjk : j < K.degree - i := by
        apply Nat.lt_sub_iff_add_lt.mpr
        simpa only [Nat.add_comm] using Nat.lt_sub_iff_add_lt.mp (lt_of_not_ge h)
      simp only [ite_eq_right h, ← Nat.choose_eq_fast_choose, Nat.choose_eq_zero_of_lt hjk,
        Nat.cast_zero, Int.cast_zero, mul_zero]
  · rw [highCompactFactored, ite_eq_right hi, ← compact_coeff_eq]
    exact
      (Polynomial.coeff_eq_zero_of_natDegree_lt
          ((high_gaussian_polynomial_degree K).trans_lt (lt_of_not_ge hi))).symm

/-- Convolve a certified compact coefficient row using the kernel normalization. -/
private def highGammaExpandAt (K : HighGaussianKernel) (c : Array ℚ) (j : ℕ) : ℚ :=
  K.normalization * ∑ ij ∈ Finset.antidiagonal j, c[ij.1]?.getD 0 * c[ij.2]?.getD 0

/-- A certified compact row can be substituted before the normalized convolution. -/
private theorem high_gamma_expanded_of_compact (K : HighGaussianKernel) (c : Array ℚ)
    (hc : (Array.ofFn (fun i : Fin (2 * K.degree + 1) ↦ highCompactFactored K i.val)) = c) :
    K.expandedCoeffRow =
      Array.ofFn (fun j : Fin (2 * K.degree + 1) ↦ highGammaExpandAt K c j.val) := by
  simp only [high_compact_factored_eq] at hc
  rw [HighGaussianKernel.expandedCoeffRow]
  simp only [highGammaExpandAt, hc]

/-- Use a checked denominator and entry values to certify the cleared profile. -/
private theorem high_gamma_profile_int_of_den (m d : ℕ) (e : Array ℚ) {H : ℕ}
    (hH : highGammaProfileDen m (highGammaBaseFrom d e) = H) (hm : m = 2 * d + 4) (b : Array ℤ)
    (hb : (Array.ofFn (fun i : Fin m ↦ clearedProfileCoeff H (highGammaBaseAt d e i.val))) = b) :
    highGammaProfileInt m (highGammaBaseFrom d e) = b := by
  rw [highGammaProfileInt, hH, ← hb]
  apply congrArg Array.ofFn
  funext i
  have hi : i.val < 2 * d + 4 := by
    rw [← hm]; exact i.isLt
  simp only [highGammaBaseFrom, Array.getElem?_ofFn, dite_eq_left hi, Option.getD_some]

/-- Compute the common denominator from already verified scalar denominators. -/
private theorem high_gamma_den_of_row (d : ℕ) (e : Array ℚ) {r : Array ℕ}
    (hr : (Array.ofFn (fun i : Fin (2 * d + 4) ↦ (highGammaBaseAt d e i.val).den)) = r) :
    highGammaProfileDen (2 * d + 4) (highGammaBaseFrom d e) =
      (Finset.range (2 * d + 4)).lcm (fun i ↦ r[i]?.getD 1) := by
  rw [← hr, highGammaProfileDen]
  apply Finset.lcm_congr rfl
  intro i hi
  have hm := Finset.mem_range.mp hi
  simp only [highGammaBaseFrom, Array.getElem?_ofFn, dite_eq_left hm, Option.getD_some]

/-- The direct unshifted row is also the input to the H28 profile checker. -/
private theorem high_gamma_base_eq_profile (K : HighGaussianKernel) :
    highGammaBaseRow K = K.cellPowerRow 0 1 := by
  apply Array.ext
  · simp only [highGammaBaseRow, highGammaBaseFrom, HighGaussianKernel.cellPowerRow,
      Array.size_ofFn]
  · intro i hB hP
    have hi : i < 2 * K.degree + 4 := by
      simpa only [highGammaBaseRow, highGammaBaseFrom, Array.size_ofFn] using hB
    have hb := high_gamma_direct_base_coeff K hi
    have hp := high_cell_power_coeff K 0 1 hi
    simp only [Polynomial.C_1, one_mul, Polynomial.C_0, add_zero, Polynomial.comp_X] at hp
    rw [← show highGammaBaseRow K = highGammaBaseFrom K.degree K.expandedCoeffRow from rfl,
      Array.getElem?_eq_getElem hB, Option.getD_some] at hb
    rw [Array.getElem?_eq_getElem hP, Option.getD_some] at hp
    exact hb.trans hp.symm

/-- Reindex the triangular H28 sum by its source power. -/
private theorem high_profile_shift_sum (m i : ℕ) (a : ℤ) (f : ℕ → ℤ) :
    (∑ k ∈ Finset.range (m - i), (Nat.fast_choose (k + i) i : ℤ) * f (k + i) * a ^ k) =
      ∑ j ∈ Finset.range m, f j * ((Nat.fast_choose j i : ℤ) * a ^ (j - i)) := by
  let g (j : ℕ) := f j * ((Nat.fast_choose j i : ℤ) * a ^ (j - i))
  have hz (j : ℕ) (hj : j < i) : g j = 0 := by
    simp only [g, ← Nat.choose_eq_fast_choose, Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, zero_mul,
      mul_zero]
  calc
    _ = ∑ k ∈ Finset.range (m - i), g (i + k) := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [g]
      rw [Nat.add_comm i k, Nat.add_sub_cancel]
      ring
    _ = ∑ j ∈ Finset.Ico i m, g j := by rw [Finset.sum_Ico_eq_sum_range]
    _ = _ :=
      Finset.sum_subset (fun j hj ↦ Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2)
        (fun j hj hj' ↦
          hz j (lt_of_not_ge fun hge ↦ hj' (Finset.mem_Ico.mpr ⟨hge, Finset.mem_range.mp hj⟩)))

/-- The shared integer shift can certify the pre-existing H28 check. -/
private theorem high_profile_check_of_int_shift (K : HighGaussianKernel) (a : ℤ)
    (h : ∀ i < 2 * K.degree + 4, 0 ≤ (highGammaShiftedProfile K a)[i]?.getD 0) :
    highIntProfileSignCheck K a = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hi' : i < 2 * K.degree + 4 := List.mem_range.mp hi
  have hi'' : i ≤ 2 * K.degree + 3 := Nat.le_of_lt_succ hi'
  have hc := h i hi'
  simp only [highGammaShiftedProfile, highGammaShiftInt, highGammaShiftCoeff, Array.getElem?_ofFn,
    dite_eq_left hi', Option.getD_some] at hc
  have hp : ∀ j ∈ Finset.range (2 * K.degree + 4), j - i < 2 * K.degree + 4 := fun j hj ↦
    (Nat.sub_le j i).trans_lt (Finset.mem_range.mp hj)
  refine decide_eq_true ?_
  simp only [← Nat.sub_add_comm hi'', ← high_gamma_base_eq_profile K]
  let f (j : ℕ) := (highGammaProfileInt (2 * K.degree + 4) (highGammaBaseRow K))[j]?.getD 0
  change
    0 ≤
      ∑ k ∈ Finset.range (2 * K.degree + 4 - i), (Nat.fast_choose (k + i) i : ℤ) * f (k + i) * a ^ k
  rw [high_profile_shift_sum]
  refine hc.trans_eq (Finset.sum_congr rfl ?_)
  intro j hj
  simp only [dite_eq_left (hp j hj), Option.getD_some, f]

/-- Read a single coefficient of the shifted profile after clearing its positive denominator. -/
public def highShiftProfileCoeff (K : HighGaussianKernel) (a : ℤ) (i : ℕ) : ℤ :=
  (highGammaShiftedProfile K a)[i]?.getD 0

/-- Nonnegative shifted coefficients certify the H28 profile check. -/
public theorem high_profile_check_of_coeffs (K : HighGaussianKernel) (a : ℤ)
    (h : ∀ i < 2 * K.degree + 4, 0 ≤ highShiftProfileCoeff K a i) :
    highIntProfileSignCheck K a = true := by exact high_profile_check_of_int_shift K a h

end PseudoPrime.PrimeTestBounds.MillerRabin
