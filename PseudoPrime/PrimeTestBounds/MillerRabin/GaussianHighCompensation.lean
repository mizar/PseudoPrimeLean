/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.BernsteinCompensation
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighPrincipalCenter
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData

/-! # Rational physical profiles for the high Gaussian compensation -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The physical profile, including the Gram normalization, over the rationals.
Its coefficients are the input to the Bernstein compensation calculation. -/
@[expose]
public noncomputable def HighGaussianKernel.ratProfile (K : HighGaussianKernel) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (2 * K.degree + 1),
    Polynomial.monomial (K.logPower j) (K.expandedCoeff j / ((K.logPower j).factorial : ℚ))

/-- Casting the rational physical profile gives the polynomial in the
centered principal term and the high Gaussian Euler sum. -/
public theorem high_comp_profile_map (K : HighGaussianKernel) :
    K.ratProfile.map (Rat.castHom ℝ) = K.realProfile := by
  simp only [HighGaussianKernel.ratProfile, HighGaussianKernel.realProfile, Polynomial.map_sum,
    Polynomial.map_monomial, Rat.coe_castHom, Rat.cast_div, Rat.cast_natCast]

/-- A computable rational coefficient of the physical profile. The sum
selects the terms at the requested log exponent. -/
@[expose]
public def HighGaussianKernel.ratProfileCoeff (K : HighGaussianKernel) (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (2 * K.degree + 1),
    if K.logPower j = k then K.expandedCoeffRat j / ((K.logPower j).factorial : ℚ) else 0

/-- The executable expression returns the coefficient of the H15 input polynomial. -/
public theorem high_rat_profile_coeff (K : HighGaussianKernel) (k : ℕ) :
    K.ratProfile.coeff k = K.ratProfileCoeff k := by
  simp only [HighGaussianKernel.ratProfile, HighGaussianKernel.ratProfileCoeff,
    Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply,
    high_expanded_coeff_rat]

/-- The largest physical monomial exponent bounds the profile degree. -/
public theorem high_rat_profile_degree (K : HighGaussianKernel) :
    K.ratProfile.natDegree ≤ 2 * K.degree + 3 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact
    (Polynomial.natDegree_monomial_le _).trans
      (Nat.add_le_add_right (Nat.sub_le (2 * K.degree) j) 3)

/-- Compute the affine cell input coefficients from rational kernel data. -/
public theorem high_rat_profile_affine_coeff (K : HighGaussianKernel) (l h : ℚ) (k : ℕ) :
    (K.ratProfile.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)).coeff k =
      h ^ k *
        ∑ j ∈ Finset.range (2 * K.degree + 4),
          K.ratProfileCoeff j * ((Nat.fast_choose j k : ℚ) * l ^ (j - k)) := by
  rw [Analysis.rational_affine_coeff _ _ (high_rat_profile_degree K)]
  simp only [high_rat_profile_coeff]

/-- Compute the power coefficients on a cell once for the Bernstein conversion. -/
@[expose]
public def HighGaussianKernel.cellPowerRow (K : HighGaussianKernel) (l h : ℚ) : Array ℚ :=
  let numerator := K.expandedCoeffRow
  let table :=
    Array.ofFn
      (fun k : Fin (2 * K.degree + 4) ↦
        ∑ j ∈ Finset.range (2 * K.degree + 1),
          if K.logPower j = k.val then numerator[j]?.getD 0 / ((K.logPower j).factorial : ℚ) else 0)
  Array.ofFn
    (fun k : Fin (2 * K.degree + 4) ↦
      h ^ k.val *
        ∑ j ∈ Finset.range (2 * K.degree + 4),
          table[j]?.getD 0 * ((Nat.fast_choose j k.val : ℚ) * l ^ (j - k.val)))

/-- Each in-range entry of the computed power row is the corresponding
coefficient of the affine rational profile. -/
public theorem high_cell_power_coeff (K : HighGaussianKernel) (l h : ℚ) {k : ℕ}
    (hk : k < 2 * K.degree + 4) :
    (K.cellPowerRow l h)[k]?.getD 0 =
      (K.ratProfile.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)).coeff k := by
  simp only [HighGaussianKernel.cellPowerRow, high_rat_profile_affine_coeff, Array.size_ofFn,
    getElem?_def, hk, dite_eq_left, Array.getElem_ofFn, Option.getD_some]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  simp only [hj', dite_eq_left, Option.getD_some, HighGaussianKernel.ratProfileCoeff]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have he := high_expanded_row_get K (Finset.mem_range.mp ha)
  simp only [getElem?_def] at he
  rw [he]

/-- Read a signed Bernstein coefficient from the shared power coefficient row. -/
@[expose]
public def cellBernsteinFromPower (n i : ℕ) (row : Array ℚ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    if k ≤ i then row[k]?.getD 0 * ((Nat.fast_choose i k : ℚ) / (Nat.fast_choose n k : ℚ)) else 0

/-- Convert the physical kernel on a rational log cell to one signed Bernstein coefficient. -/
@[expose]
public def HighGaussianKernel.cellBernsteinCoeff (K : HighGaussianKernel) (l h : ℚ) (i : ℕ) : ℚ :=
  cellBernsteinFromPower (2 * K.degree + 3) i (K.cellPowerRow l h)

/-- The direct rational conversion computes the Bernstein coefficient of
the affine polynomial used in the analytic cell bounds. -/
public theorem high_cell_bernstein_coeff (K : HighGaussianKernel) (l h : ℚ) (i : ℕ) :
    Analysis.bernsteinRatCoeff (K.ratProfile.comp (Polynomial.C h * Polynomial.X + Polynomial.C l))
        (2 * K.degree + 3) i =
      K.cellBernsteinCoeff l h i := by
  simp only [Analysis.bernsteinRatCoeff, HighGaussianKernel.cellBernsteinCoeff,
    cellBernsteinFromPower]
  apply Finset.sum_congr rfl
  intro k hk'
  by_cases hk : k ≤ i
  · rw [ite_eq_left hk, high_cell_power_coeff K l h (Finset.mem_range.mp hk')]
  · simp only [ite_eq_right hk, ← Nat.choose_eq_fast_choose,
      Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk), Nat.cast_zero, zero_div, mul_zero]

/-- The clipped affine profile is nonnegative and offsets the physical
kernel on each rational cell of the high Gaussian partition. -/
public theorem high_bernstein_compensation_nonneg (K : HighGaussianKernel) (l r : ℚ)
    (t : Set.Icc (0 : ℝ) 1) :
    let C :=
      Analysis.bernsteinCompensation
        (K.ratProfile.comp (Polynomial.C (r - l) * Polynomial.X + Polynomial.C l))
        (2 * K.degree + 3)
    0 ≤ C.eval (t : ℝ) ∧
      0 ≤ K.realProfile.eval (((r - l : ℚ) : ℝ) * t + (l : ℝ)) + C.eval (t : ℝ) := by
  simpa only [← Polynomial.eval_map, high_comp_profile_map] using
    Analysis.bernstein_affine_compensation_nonneg _ _ (high_rat_profile_degree K) l r t

/-- In the log coordinate used by the Abel integral, the high compensation
and the compensated physical profile are nonnegative throughout the cell. -/
public theorem high_compensation_cell_nonneg (K : HighGaussianKernel) (l r : ℚ) (hlr : l < r)
    {v : ℝ} (hv : v ∈ Set.Icc (l : ℝ) (r : ℝ)) :
    let C :=
      Analysis.bernsteinCompensation
        (K.ratProfile.comp (Polynomial.C (r - l) * Polynomial.X + Polynomial.C l))
        (2 * K.degree + 3)
    let u := (v - (l : ℝ)) / ((r - l : ℚ) : ℝ)
    0 ≤ C.eval u ∧ 0 ≤ K.realProfile.eval v + C.eval u := by
  have h : (0 : ℝ) < ((r - l : ℚ) : ℝ) := Rat.cast_pos.mpr (sub_pos.mpr hlr)
  have hu : v - (l : ℝ) ≤ ((r - l : ℚ) : ℝ) := by
    rw [Rat.cast_sub]
    exact sub_le_sub_right hv.2 _
  let t : Set.Icc (0 : ℝ) 1 := ⟨_, div_nonneg (sub_nonneg.mpr hv.1) h.le, (div_le_one h).mpr hu⟩
  have ht : ((r - l : ℚ) : ℝ) * (t : ℝ) + (l : ℝ) = v := by
    change ((r - l : ℚ) : ℝ) * ((v - (l : ℝ)) / ((r - l : ℚ) : ℝ)) + (l : ℝ) = v
    rw [mul_div_cancel₀ _ h.ne', sub_add_cancel]
  simpa only [ht] using high_bernstein_compensation_nonneg K l r t

/-- For a positive-width log cell with nonnegative left endpoint, the
normalized main and variation charges are bounded by rational Taylor moments. -/
public theorem high_compensation_cell_bounds (K : HighGaussianKernel) {l h : ℚ} (hl : 0 ≤ l)
    (hh : 0 < h) :
    let n := 2 * K.degree + 3
    let P := K.ratProfile.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)
    let C := Analysis.bernsteinCompensation P n
    let u := fun v : ℝ ↦ (v - (l : ℝ)) / (h : ℝ)
    let s : ℚ := K.pole + 1 / 2
    let d : ℚ := K.pole - 1 / 2
    (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ), Real.exp (-(s : ℝ) * v) * C.eval (u v)) ≤
        (↑(Analysis.compensationExpUpper (s * l) *
              Analysis.compensationMomentSum n 2 h s
                (fun i ↦ max 0 (-Analysis.bernsteinRatCoeff P n i.val))) :
          ℝ) ∧
      (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ),
          Real.exp (-(K.pole : ℝ) * v) *
            |(d : ℝ) * C.eval (u v) - (h : ℝ)⁻¹ * C.derivative.eval (u v)|) ≤
        (↑(Analysis.compensationExpUpper (K.pole * l) *
              Analysis.compensationMomentSum n 1 h K.pole
                (fun i ↦
                  |Analysis.bernsteinRatCoeff (Analysis.bernsteinRatVariation P n d h) n i.val|)) :
          ℝ) := by
  have hp :=
    Rat.cast_nonneg.mp ((by norm_num only : (0 : ℝ) ≤ 1 / 2).trans (high_gaussian_pole_gt K).le)
  have hdeg := Analysis.bernstein_affine_degree _ _ (high_rat_profile_degree K) l (l + h)
  rw [add_sub_cancel_left] at hdeg
  exact
    ⟨Analysis.bernstein_compensation_rat_cell_le _ _ hdeg hh hl (add_nonneg hp (by norm_num only)),
      Analysis.bernstein_variation_rat_cell_le _ _ _ hh hl hp⟩

/-- The rational main charge assigned to one high Gaussian log cell. -/
@[expose]
public def HighGaussianKernel.cellMainBound (K : HighGaussianKernel) (l h : ℚ) : ℚ :=
  let s := K.pole + 1 / 2
  let n := 2 * K.degree + 3
  let row := K.cellPowerRow l h
  let c := Array.ofFn (fun i : Fin (n + 1) ↦ max 0 (-cellBernsteinFromPower n i.val row))
  Analysis.compensationExpUpper (s * l) *
    Analysis.compensationMomentSum n 2 h s (fun i ↦ c[i.val]'(Array.size_ofFn.symm ▸ i.isLt))

/-- The directly computed rational charge bounds the weighted compensation
integral for the cell, with the Gram normalization already included. -/
public theorem high_compensation_main_le (K : HighGaussianKernel) {l h : ℚ} (hl : 0 ≤ l)
    (hh : 0 < h) :
    let P := K.ratProfile.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)
    let C := Analysis.bernsteinCompensation P (2 * K.degree + 3)
    (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ),
        Real.exp (-((K.pole + 1 / 2 : ℚ) : ℝ) * v) * C.eval ((v - (l : ℝ)) / (h : ℝ))) ≤
      (K.cellMainBound l h : ℝ) := by
  simpa only [HighGaussianKernel.cellMainBound, Array.getElem_ofFn, high_cell_bernstein_coeff,
    HighGaussianKernel.cellBernsteinCoeff] using (high_compensation_cell_bounds K hl hh).1

/-- The rational variation charge of a cell, computed from the clipped
coefficients after combining the compensation and derivative terms. -/
@[expose]
public def HighGaussianKernel.cellVariationBound (K : HighGaussianKernel) (l h : ℚ) : ℚ :=
  let n := 2 * K.degree + 3
  let row := K.cellPowerRow l h
  let c := Array.ofFn (fun i : Fin (n + 1) ↦ max 0 (-cellBernsteinFromPower n i.val row))
  let p :=
    Analysis.bernsteinVariationPowerRow n (K.pole - 1 / 2) h
      (fun j ↦ c[j.val]'(Array.size_ofFn.symm ▸ j.isLt))
  let v := Array.ofFn (fun i : Fin (n + 1) ↦ |Analysis.bernsteinVariationFromRow n i.val p|)
  Analysis.compensationExpUpper (K.pole * l) *
    Analysis.compensationMomentSum n 1 h K.pole (fun i ↦ v[i.val]'(Array.size_ofFn.symm ▸ i.isLt))

/-- The computed rational charge bounds the weighted variation integral
of the high Gaussian compensation on the cell. -/
public theorem high_compensation_variation_le (K : HighGaussianKernel) {l h : ℚ} (hl : 0 ≤ l)
    (hh : 0 < h) :
    let C :=
      Analysis.bernsteinCompensation
        (K.ratProfile.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)) (2 * K.degree + 3)
    let u := fun v : ℝ ↦ (v - (l : ℝ)) / (h : ℝ)
    (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ),
        Real.exp (-(K.pole : ℝ) * v) *
          |((K.pole - 1 / 2 : ℚ) : ℝ) * C.eval (u v) - (h : ℝ)⁻¹ * C.derivative.eval (u v)|) ≤
      (K.cellVariationBound l h : ℝ) := by
  simpa only [HighGaussianKernel.cellVariationBound, Array.getElem_ofFn,
    Analysis.bernstein_variation_row_eq, Analysis.bernstein_variation_coeff_eq,
    high_cell_bernstein_coeff, HighGaussianKernel.cellBernsteinCoeff] using
    (high_compensation_cell_bounds K hl hh).2

/-- Evaluate the physical profile at a rational argument using the
shared square-numerator coefficient row. -/
@[expose]
public def HighGaussianKernel.ratProfileValue (K : HighGaussianKernel) (x : ℚ) : ℚ :=
  let row := K.expandedCoeffRow
  ∑ j ∈ Finset.range (2 * K.degree + 1),
    row[j]?.getD 0 / ((K.logPower j).factorial : ℚ) * x ^ K.logPower j

/-- The rational evaluation agrees with the physical profile in the Euler sum. -/
public theorem high_rat_profile_value_eq (K : HighGaussianKernel) (x : ℚ) :
    K.realProfile.eval (x : ℝ) = (K.ratProfileValue x : ℝ) := by
  simp only [HighGaussianKernel.realProfile, HighGaussianKernel.ratProfileValue,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_pow]
  apply Finset.sum_congr rfl
  intro j hj
  rw [high_expanded_row_get K (Finset.mem_range.mp hj), high_expanded_coeff_rat]

private theorem k186_endpoint_pos : 0 < HighGaussianKernel.k186.ratProfileValue 5 := by
  decide +kernel

private theorem k196_endpoint_pos : 0 < HighGaussianKernel.k196.ratProfileValue 5 := by
  decide +kernel

/-- Both high physical profiles are positive at the right endpoint.
The sign is checked by exact rational evaluation of the numerator row. -/
public theorem high_real_profile_at_five_pos (K : HighGaussianKernel) :
    0 < K.realProfile.eval 5 := by
  have h : 0 < K.ratProfileValue 5 := by
    cases K
    · exact k186_endpoint_pos
    · exact k196_endpoint_pos
  have he : K.realProfile.eval 5 = (K.ratProfileValue 5 : ℝ) := by
    simpa only [Rat.cast_ofNat] using high_rat_profile_value_eq K 5
  exact he.symm ▸ Rat.cast_pos.mpr h

end PseudoPrime.PrimeTestBounds.MillerRabin
