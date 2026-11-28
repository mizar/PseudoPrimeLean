/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms

/-! # Integer affine rows for the bounded K186 Abel integrals -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The coefficient 1-norm bounds a polynomial on the unit interval
centered at zero, using a fixed degree bound for the finite sum. -/
private theorem abs_eval_le_coeff_sum (P : Polynomial ℝ) {N : ℕ} (hN : P.natDegree < N) {t : ℝ}
    (ht : |t| ≤ 1) : |P.eval t| ≤ ∑ i ∈ Finset.range N, |P.coeff i| := by
  rw [Polynomial.eval_eq_sum_range' hN]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [abs_mul, abs_pow]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) ht)

/-- Integrate an absolute polynomial against a decaying exponential on a
cell. The midpoint affine row is evaluated on the interval from -1 to 1. -/
public theorem abel_abs_cell_le (P : Polynomial ℝ) {s l u E : ℝ} (hs : 0 ≤ s) (hlu : l < u)
    (hE : Real.exp (-s * l) ≤ E) {N : ℕ}
    (hN :
      (P.comp (Polynomial.C ((u - l) / 2) * Polynomial.X + Polynomial.C ((l + u) / 2))).natDegree <
        N) :
    let Q := P.comp (Polynomial.C ((u - l) / 2) * Polynomial.X + Polynomial.C ((l + u) / 2))
    (∫ t in l..u, Real.exp (-s * t) * |P.eval t|) ≤
      (u - l) * (E * ∑ i ∈ Finset.range N, |Q.coeff i|) := by
  intro Q
  let C := ∑ i ∈ Finset.range N, |Q.coeff i|
  have hc : Continuous (fun t : ℝ ↦ Real.exp (-s * t) * |P.eval t|) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul P.continuous.abs
  calc
    _ ≤ ∫ _ in l..u, E * C := by
      apply
        intervalIntegral.integral_mono_on hlu.le (hc.intervalIntegrable l u)
          (continuous_const.intervalIntegrable l u)
      intro t ht
      let r := (u - l) / 2
      let m := (l + u) / 2
      have hr : 0 < r := half_pos (sub_pos.mpr hlu)
      have hv : |(t - m) / r| ≤ 1 :=
        abs_le.mpr
          ⟨(le_div_iff₀ hr).mpr
              (by
                dsimp only [m, r]; linarith only [ht.1]),
            (div_le_iff₀ hr).mpr
              (by
                dsimp only [m, r]; linarith only [ht.2])⟩
      have hP := abs_eval_le_coeff_sum Q hN hv
      have he : Q.eval ((t - m) / r) = P.eval t := by
        simp only [Q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_X]
        change P.eval (r * ((t - m) / r) + m) = P.eval t
        rw [mul_div_cancel₀ _ hr.ne', sub_add_cancel]
      rw [he] at hP
      have he' :=
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.mpr hs))).trans hE
      exact mul_le_mul he' hP (abs_nonneg _) ((Real.exp_nonneg _).trans hE)
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]

/-- For integer endpoints the midpoint row uses denominator two.
The verification reduces to the sum of absolute integer numerators. -/
public theorem abel_int_cell_le (row : MiddleIntRow) (N : ℕ) {l u : ℤ} (hd : 0 < row.den)
    (hlu : l < u) {s E : ℝ} (hs : 0 ≤ s) (hE : Real.exp (-s * (l : ℝ)) ≤ E) :
    let P := (row.poly N).map (Rat.castHom ℝ)
    let A := row.affine N (l + u) (u - l) 2
    (∫ t in (l : ℝ)..(u : ℝ), Real.exp (-s * t) * |P.eval t|) ≤
      ((u : ℝ) - l) * (E * ((∑ i ∈ Finset.range (N + 1), |A.num i| : ℤ) : ℝ) / A.den) := by
  intro P A
  have hpoly :
    (A.poly N).map (Rat.castHom ℝ) =
      P.comp
        (Polynomial.C (((u : ℝ) - l) / 2) * Polynomial.X + Polynomial.C (((l : ℝ) + u) / 2)) := by
    have he := row.poly_affine N (l + u) (u - l) 2 hd.ne' (by decide)
    rw [show A = row.affine N (l + u) (u - l) 2 from rfl, he]
    simp only [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Rat.coe_castHom, Rat.cast_div, Rat.cast_intCast, Int.cast_add, Int.cast_sub,
      Int.cast_ofNat, Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat, P]
  have hN : ((A.poly N).map (Rat.castHom ℝ)).natDegree < N + 1 := by
    rw [Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℝ).injective]
    exact Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _
  have h := abel_abs_cell_le P hs (Int.cast_lt.mpr hlu) hE (hpoly ▸ hN)
  dsimp only at h
  rw [← hpoly] at h
  have hden : (0 : ℝ) < A.den := Int.cast_pos.mpr (mul_pos hd (pow_pos (by decide : (0 : ℤ) < 2) _))
  have hsum :
    (∑ i ∈ Finset.range (N + 1), |((A.poly N).map (Rat.castHom ℝ)).coeff i|) =
      ((∑ i ∈ Finset.range (N + 1), |A.num i| : ℤ) : ℝ) / A.den := by
    rw [Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.coeff_map, Rat.coe_castHom,
      A.poly_coeff (Nat.le_of_lt_succ (Finset.mem_range.mp hi)), Rat.cast_div, Rat.cast_intCast,
      Rat.cast_intCast, abs_div, abs_of_pos hden, Int.cast_abs]
  rw [hsum] at h
  simpa only [mul_div_assoc] using h

/-- An integer lower bound on the magnitude of the negative exponent
gives a rational upper bound used in the cell checker. -/
private theorem exp_neg_le_rational_pow {v : ℝ} {e : ℕ} (he : (e : ℝ) ≤ v) :
    Real.exp (-v) ≤ (10 / 27 : ℝ) ^ e := by
  have h := Real.exp_le_exp.mpr (neg_le_neg he)
  have h₁ : Real.exp (-1) ≤ (10 / 27 : ℝ) := by
    rw [Real.exp_neg, ← one_div]
    exact
      (one_div_le_one_div_of_le (by norm_num only)
            ((by norm_num only : (27 / 10 : ℝ) ≤ 2.7182818283).trans
              Real.exp_one_gt_d9.le)).trans_eq
        (by norm_num only)
  rw [show -(e : ℝ) = (e : ℝ) * (-1) by ring, Real.exp_natCast_mul] at h
  exact h.trans (pow_le_pow_left₀ (Real.exp_pos _).le h₁ _)

/-- Cross-multiplication of the integer cell inequality supplies a genuine
integral cap with no rational coefficient calculation in the receiver. -/
public theorem abel_int_cell_of_check (row : MiddleIntRow) (N : ℕ) {l u cap : ℤ} {e : ℕ} {s : ℝ}
    (hd : 0 < row.den) (hlu : l < u) (hs : 0 ≤ s) (he : (e : ℝ) ≤ s * (l : ℝ))
    (hc :
      let A := row.affine N (l + u) (u - l) 2
      (u - l) * (∑ i ∈ Finset.range (N + 1), |A.num i|) * 10 ^ e ≤ cap * A.den * 27 ^ e) :
    let P := (row.poly N).map (Rat.castHom ℝ)
    (∫ t in (l : ℝ)..(u : ℝ), Real.exp (-s * t) * |P.eval t|) ≤ (cap : ℝ) := by
  have hE := exp_neg_le_rational_pow he
  rw [← neg_mul] at hE
  have h := abel_int_cell_le row N hd hlu hs hE
  let A := row.affine N (l + u) (u - l) 2
  let S := ((∑ i ∈ Finset.range (N + 1), |A.num i| : ℤ) : ℝ)
  have hA : 0 < (A.den : ℝ) := Int.cast_pos.mpr (mul_pos hd (pow_pos (by decide) N))
  have h27 : 0 < (27 : ℝ) ^ e := pow_pos (by norm_num only) _
  have hcR := (Int.cast_le (R := ℝ)).mpr hc
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_ofNat] at hcR
  refine h.trans ?_
  change ((u : ℝ) - l) * ((10 / 27 : ℝ) ^ e * S / A.den) ≤ (cap : ℝ)
  have hx : ((u : ℝ) - l) * S * 10 ^ e ≤ (cap : ℝ) * (A.den : ℝ) * 27 ^ e := hcR
  rw [div_pow, div_mul_eq_mul_div, div_div, ← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos h27 hA)).mpr
  simpa only [mul_assoc, mul_comm ((27 : ℝ) ^ e), mul_comm ((10 : ℝ) ^ e)] using hx

end PseudoPrime.PrimeTestBounds.MillerRabin
