/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleBernstein
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
public import PseudoPrime.Analysis.PositiveTaylorTransport

/-! # Integer certificates for the absolute middle Laplace tails -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Bound a complete exponential tail by the absolute coefficients of its
translated integer row and any rational upper bound on the endpoint exponential. -/
public theorem MiddleIntRow.abs_tail_le (r : MiddleIntRow) (N : ℕ) (a b : ℤ) (hr : r.den ≠ 0)
    (hb : b ≠ 0) {s E : ℚ} (hs : 0 < s)
    (hE : Real.exp (-(s : ℝ) * (((a : ℚ) / b : ℚ) : ℝ)) ≤ (E : ℝ)) :
    let z := ((a : ℚ) / b : ℚ)
    let q := r.shift N a b
    (∫ t in Set.Ioi (z : ℝ), Real.exp (-(s : ℝ) * t) * |(r.poly N).eval₂ (Rat.castHom ℝ) t|) ≤
      ((E *
          ∑ i ∈ Finset.range (N + 1), |(q.num i : ℚ) / q.den| * ((i.factorial : ℚ) / s ^ (i + 1))) :
        ℚ) := by
  intro z q
  let P := (r.poly N).map (Rat.castHom ℝ)
  let Q := (q.poly N).map (Rat.castHom ℝ)
  have he : Q = P.comp (Polynomial.X + Polynomial.C (z : ℝ)) := by
    dsimp only [Q, q, P, z]
    rw [r.poly_shift N a b hr hb, Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X,
      Polynomial.map_C, Rat.coe_castHom]
  have hN : Q.natDegree ≤ N :=
    Polynomial.natDegree_map_le.trans
      (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _))
  have ht := abs_laplace_tail_le_coeffs P (Rat.cast_pos.mpr hs) (z : ℝ)
  dsimp only at ht
  rw [← he] at ht
  have hp :
    (∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i| * ((i.factorial : ℝ) / (s : ℝ) ^ (i + 1))) ≤
      ∑ i ∈ Finset.range (N + 1), |Q.coeff i| * ((i.factorial : ℝ) / (s : ℝ) ^ (i + 1)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.succ_le_succ hN))
      (fun i _ _ ↦
        mul_nonneg (abs_nonneg _)
          (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Rat.cast_nonneg.mpr hs.le) _)))
  rw [Rat.cast_mul, Rat.cast_sum]
  simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_abs, Rat.cast_pow, Rat.cast_natCast]
  have hf (i : ℕ) (hi : i ∈ Finset.range (N + 1)) :
    Q.coeff i = (((q.num i : ℚ) / q.den : ℚ) : ℝ) := by
    dsimp only [Q]
    rw [Polynomial.coeff_map, q.poly_coeff (Nat.le_of_lt_succ (Finset.mem_range.mp hi)),
      Rat.coe_castHom]
  have hsum :=
    Finset.sum_congr rfl
      (fun i hi ↦ congrArg (fun v : ℝ ↦ |v| * ((i.factorial : ℝ) / (s : ℝ) ^ (i + 1))) (hf i hi))
  simp only [Rat.cast_div] at hsum
  rw [← hsum]
  have hn : 0 ≤ ∑ i ∈ Finset.range (N + 1), |Q.coeff i| * ((i.factorial : ℝ) / (s : ℝ) ^ (i + 1)) :=
    Finset.sum_nonneg
      (fun _ _ ↦
        mul_nonneg (abs_nonneg _)
          (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Rat.cast_nonneg.mpr hs.le) _)))
  simp only [P, Polynomial.eval_map] at ht
  exact
    (ht.trans (mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _))).trans
      (mul_le_mul_of_nonneg_right hE hn)

/-- A positive rational Taylor subtotal can certify an upper bound for the
negative exponential. Use one such comparison for each shared grid ratio. -/
public theorem middle_exp_neg_le_of_taylor {t R : ℚ} (n : ℕ) (ht : 0 ≤ t) (hR : 0 < R)
    (h : R⁻¹ ≤ Analysis.gammaPositiveTaylor t n) : Real.exp (-(t : ℝ)) ≤ (R : ℝ) := by
  have hr : (0 : ℝ) < R := Rat.cast_pos.mpr hR
  have he := ((Rat.cast_le (K := ℝ)).mpr h).trans (Analysis.gamma_positive_taylor_le_exp ht n)
  rw [Rat.cast_inv] at he
  rw [Real.exp_neg, ← inv_inv (R : ℝ)]
  exact (inv_le_inv₀ (Real.exp_pos _) (inv_pos.mpr hr)).mpr he

/-- A rational positive-exponential comparison uses the Taylor subtotal and
twice the next term when the ratios in the tail are at most one half. -/
public theorem middle_exp_le_of_taylor {t U : ℚ} (n : ℕ) (ht : 0 ≤ t) (hn : t / (n + 1 : ℕ) ≤ 1 / 2)
    (h : Analysis.gammaPositiveTaylor t n + t ^ n / (n.factorial : ℚ) * 2 ≤ U) :
    Real.exp (t : ℝ) ≤ (U : ℝ) := by
  have ha := (Rat.cast_le (K := ℝ)).mpr hn
  have hu := (Rat.cast_le (K := ℝ)).mpr h
  simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] at ha
  simp only [Analysis.gammaPositiveTaylor, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hu
  exact (Analysis.exp_le_taylor_add_two_next (Rat.cast_nonneg.mpr ht) ha).trans hu

/-- A single certified quarter-step ratio bounds every negative quarter-integer
exponent needed in the physical remainder. -/
public theorem middle_exp_neg_quarters_le (n : ℕ) :
    Real.exp (-(n : ℝ) / 4) ≤ ((778801 / 10 ^ 6 : ℚ) ^ n : ℚ) := by
  have hr :=
    middle_exp_neg_le_of_taylor (t := 1 / 4) (R := 778801 / 10 ^ 6) 16 (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have h := middle_exp_grid_le (a := 0) (by rw [Real.exp_zero]) hr n
  simp only [zero_add, one_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow] at h ⊢
  convert h using 2
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
