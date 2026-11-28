/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassProfile
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianOppositeCoeffFast
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassRational
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassProfile
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPolynomial

/-! # Shared coefficient computation for the middle Gaussian mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Store all powers of the compact numerator's two coefficient parts. -/
private def middlePartRows (a : ℚ) (d : ℕ) (width : ℕ) : Array (Array (ℚ × ℚ)) :=
  recurrenceRows (partRow a width 0) #[]
    (fun _ prev ↦
      Array.ofFn
        (fun i : Fin width ↦
          let (A, B) := prev[i.val]?.getD (0, 0)
          let T := if 1 ≤ i.val then (prev[i.val - 1]?.getD (0, 0)).2 else 0
          (a * A + (a ^ 2 * B - T), A + a * B)))
    d

/-- An entry of the shared table gives the same two coefficients. -/
private theorem middle_part_rows_eq (a : ℚ) (d : ℕ) (width k : ℕ) (hk : k ≤ d) :
    (middlePartRows a d width)[k]?.getD #[] = partRow a width k := by
  unfold middlePartRows
  exact recurrence_rows_eq _ _ _ (partRow a width) rfl (fun _ ↦ rfl) d k hk

/-- Evaluate both numerator parts for all coefficient indices needed in the mass. -/
private def middlePartsTable (a : ℚ) (d : ℕ) (f : ℕ → ℚ) : Array (ℚ × ℚ) :=
  let rows := middlePartRows a d (d + 1)
  let cf := Array.ofFn (fun k : Fin (d + 1) ↦ f k.val)
  Array.ofFn
    (fun i : Fin (d + 1) ↦
      (∑ k ∈ Finset.range (d + 1), cf[k]?.getD 0 * (((rows[k]?.getD #[])[i.val]?).getD (0, 0)).1,
        ∑ k ∈ Finset.range (d + 1), cf[k]?.getD 0 * (((rows[k]?.getD #[])[i.val]?).getD (0, 0)).2))

/-- Shared numerator computation agrees with the scalar numerator calculation. -/
private theorem middle_parts_table_eq (a : ℚ) (d : ℕ) (f : ℕ → ℚ) (i : ℕ) (hi : i ≤ d) :
    (middlePartsTable a d f)[i]?.getD (0, 0) =
      (∑ k ∈ Finset.range (d + 1), f k * ((partRow a (i + 1) k)[i]?.getD (0, 0)).1,
        ∑ k ∈ Finset.range (d + 1), f k * ((partRow a (i + 1) k)[i]?.getD (0, 0)).2) := by
  have h (k : ℕ) (hk : k ∈ Finset.range (d + 1)) :
    (middlePartRows a d (d + 1))[k]?.getD #[] = partRow a (d + 1) k :=
    middle_part_rows_eq a d _ k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  simp only [middlePartsTable, Array.getElem?_ofFn, dite_eq_left (Nat.lt_succ_of_le hi),
    Option.getD_some]
  apply Prod.ext
  · dsimp only
    apply Finset.sum_congr rfl
    intro k hk
    rw [dite_eq_left (Finset.mem_range.mp hk), Option.getD_some, h k hk,
      part_row_eq _ _ _ _ (Nat.lt_succ_of_le hi), part_row_eq _ _ _ _ (Nat.lt_succ_self i)]
  · dsimp only
    apply Finset.sum_congr rfl
    intro k hk
    rw [dite_eq_left (Finset.mem_range.mp hk), Option.getD_some, h k hk,
      part_row_eq _ _ _ _ (Nat.lt_succ_of_le hi), part_row_eq _ _ _ _ (Nat.lt_succ_self i)]

/-- All needed coefficients of the squared numerator share the same two input arrays. -/
private def middleNormTable (a : ℚ) (d : ℕ) (f : ℕ → ℚ) : Array ℚ :=
  let parts := middlePartsTable a d f
  let A := fun j ↦ (parts[j]?.getD (0, 0)).1
  let B := fun j ↦ (parts[j]?.getD (0, 0)).2
  let conv := fun (f : ℕ → ℚ) j ↦ ∑ v ∈ Finset.antidiagonal j, f v.1 * f v.2
  Array.ofFn
    (fun i : Fin (d + 1) ↦
      conv A i.val + ((if 1 ≤ i.val then conv B (i.val - 1) else 0) - a ^ 2 * conv B i.val))

/-- Both parts of the numerator are recovered from an input row that
agrees with the compact polynomial through the prescribed degree. -/
private theorem middle_parts_coeff (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (f : ℕ → ℚ)
    (hQ : Q.natDegree ≤ d) (hf : ∀ k ≤ d, f k = Q.coeff k) (i : ℕ) (hi : i ≤ d) :
    (middlePartsTable a d f)[i]?.getD (0, 0) =
      ((polynomialParts a Q).1.coeff i, (polynomialParts a Q).2.coeff i) := by
  rw [middle_parts_table_eq a d f i hi]
  have hsum (g : ℕ → ℚ) :
    (∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * g k) =
      ∑ k ∈ Finset.range (d + 1), f k * g k := by
    calc
      _ = ∑ k ∈ Finset.range (d + 1), Q.coeff k * g k := by
        apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hQ))
        intro k _ hk
        have h := Nat.le_of_not_gt (fun h ↦ hk (Finset.mem_range.mpr h))
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le h), zero_mul]
      _ = _ :=
        Finset.sum_congr rfl fun k hk ↦ by rw [hf k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
  simp only [polynomialParts, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    part_row_eq _ _ _ _ (Nat.lt_succ_self i)]
  apply Prod.ext
  · have h (k : ℕ) : (powerParts a k).1.coeff i = (partCoeff a k i).1 :=
      congrArg Prod.fst (part_coeff_eq a k i)
    simp only [h]
    exact (hsum _).symm
  · have h (k : ℕ) : (powerParts a k).2.coeff i = (partCoeff a k i).2 :=
      congrArg Prod.snd (part_coeff_eq a k i)
    simp only [h]
    exact (hsum _).symm

/-- The shared convolution gives the corresponding coefficient of the absolute numerator. -/
private theorem middle_norm_coeff (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (f : ℕ → ℚ)
    (hQ : Q.natDegree ≤ d) (hf : ∀ k ≤ d, f k = Q.coeff k) (i : ℕ) (hi : i ≤ d) :
    (middleNormTable a d f)[i]?.getD 0 = (normSqPolynomial a Q).coeff i := by
  let AB := polynomialParts a Q
  have h₁ (j : ℕ) (hj : j ≤ d) : ((middlePartsTable a d f)[j]?.getD (0, 0)).1 = AB.1.coeff j :=
    congrArg Prod.fst (middle_parts_coeff Q a d f hQ hf j hj)
  have h₂ (j : ℕ) (hj : j ≤ d) : ((middlePartsTable a d f)[j]?.getD (0, 0)).2 = AB.2.coeff j :=
    congrArg Prod.snd (middle_parts_coeff Q a d f hQ hf j hj)
  change _ = (AB.1 ^ 2 + (Polynomial.X - Polynomial.C (a ^ 2)) * AB.2 ^ 2).coeff i
  have hx := Polynomial.coeff_X_pow_mul' (AB.2 ^ 2) 1 i
  simp only [pow_one] at hx
  rw [Polynomial.coeff_add, sub_mul, Polynomial.coeff_sub, hx, Polynomial.coeff_C_mul]
  simp only [middleNormTable, Array.getElem?_ofFn, dite_eq_left (Nat.lt_succ_of_le hi),
    Option.getD_some, pow_two, Polynomial.coeff_mul]
  rw [convolution_congr (fun j hj ↦ h₁ j (hj.trans hi)),
    convolution_congr (fun j hj ↦ h₂ j (hj.trans ((Nat.sub_le i 1).trans hi))),
    convolution_congr (fun j hj ↦ h₂ j (hj.trans hi))]

/-- Build the mass coefficient row from one shared numerator convolution.
The mixed-pole coefficients use binomial evaluation rather than recursive expansion. -/
public def middleMassCoeffRow (a : ℚ) (d : ℕ) (f : ℕ → ℚ) : Array ℚ :=
  let numer := middleNormTable a d f
  Array.ofFn fun i : Fin (d + 2) ↦
    ∑ j ∈ Finset.range (d + 1),
      let m := d + 2 - j
      numer[j]?.getD 0 * oppositeCoeffFast a m m i.val

/-- Each in-range entry of the executable mass row equals the formal coefficient. -/
public theorem middle_mass_coeff_row_eq (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (f : ℕ → ℚ)
    (hQ : Q.natDegree ≤ d) (hf : ∀ k ≤ d, f k = Q.coeff k) {i : ℕ} (hi : i < d + 2) :
    (middleMassCoeffRow a d f)[i]?.getD 0 = (middleMassPolynomial Q a d).coeff i := by
  simp only [middleMassCoeffRow, Array.getElem?_ofFn, dite_eq_left hi, Option.getD_some,
    middleMassPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [middle_norm_coeff Q a d f hQ hf j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)),
    oppositeCoeffFast_eq, opposite_pole_coeff_eq]

end PseudoPrime.PrimeTestBounds.MillerRabin
