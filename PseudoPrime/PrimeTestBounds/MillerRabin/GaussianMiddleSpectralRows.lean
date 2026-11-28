/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleWeights
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms

/-! # Rational row certificates for the middle principal spectrum -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Absolute coefficient of the derivative of a rational profile row. -/
@[expose]
public def MiddleIntRow.spectralFullCoeff (r : MiddleIntRow) (j : ℕ) : ℚ :=
  |(r.num (j + 1) : ℚ) * (j + 1 : ℕ)| / |(r.den : ℚ)|

/-- Absolute reflected derivative coefficient of an already translated row. -/
@[expose]
public def MiddleIntRow.spectralCutCoeff (q : MiddleIntRow) (d : ℚ) (j : ℕ) : ℚ :=
  |d * q.num j - (q.num (j + 1) : ℚ) * (j + 1 : ℕ)| / |(q.den : ℚ)|

/-- The full coefficient formula recovers the derivative of the source row. -/
private theorem spectral_full_coeff_eq (r : MiddleIntRow) (N : ℕ) (hs : r.nums.size ≤ N + 1)
    (j : ℕ) :
    |((r.poly N).map (Rat.castHom ℝ)).derivative.coeff j| = (r.spectralFullCoeff j : ℝ) := by
  have h : ((r.poly N).derivative.coeff j) = ((r.num (j + 1) : ℚ) / r.den) * (j + 1 : ℕ) := by
    rw [Polynomial.coeff_derivative, r.poly_coeff_all N hs]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [Polynomial.derivative_map, Polynomial.coeff_map, h]
  simp only [Rat.coe_castHom, MiddleIntRow.spectralFullCoeff, Rat.cast_abs, Rat.cast_mul,
    Rat.cast_div, Rat.cast_natCast, abs_div, div_mul_eq_mul_div]

/-- The reflected derivative commutes with a translation, so the second
coefficient row can be checked independently of the cutoff. -/
private theorem spectral_cut_coeff_eq (r q : MiddleIntRow) (N : ℕ) {a b : ℤ} (hr : r.den ≠ 0)
    (hb : b ≠ 0) (hq : (r.shift N a b).poly N = q.poly N) (hs : q.nums.size ≤ N + 1) (d : ℚ)
    (j : ℕ) :
    let B := (r.poly N).map (Rat.castHom ℝ)
    let C := Polynomial.C (d : ℝ) * B - B.derivative
    |(C.comp (Polynomial.X + Polynomial.C (((a : ℚ) / b : ℚ) : ℝ))).coeff j| =
      (q.spectralCutCoeff d j : ℝ) := by
  intro B C
  let z := (a : ℚ) / b
  let L := Polynomial.X + Polynomial.C (z : ℝ)
  have H : B.comp L = (q.poly N).map (Rat.castHom ℝ) := by
    have h := congrArg (Polynomial.map (Rat.castHom ℝ)) (r.poly_shift N a b hr hb)
    rw [hq, Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Rat.coe_castHom] at h
    exact h.symm
  have hc : C.comp L = Polynomial.C (d : ℝ) * (B.comp L) - (B.comp L).derivative := by
    dsimp only [C]
    rw [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.derivative_comp]
    simp only [L, Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C,
      add_zero, one_mul]
  have hm :
    (Polynomial.C d * q.poly N - (q.poly N).derivative).coeff j =
      (d * q.num j - (q.num (j + 1) : ℚ) * (j + 1 : ℕ)) / q.den := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_derivative,
      q.poly_coeff_all N hs, q.poly_coeff_all N hs]
    simp only [Nat.cast_add, Nat.cast_one, mul_div_assoc, div_mul_eq_mul_div, sub_div]
  change |(C.comp L).coeff j| = _
  have hd : (Polynomial.C d).map (Rat.castHom ℝ) = Polynomial.C (d : ℝ) := by
    simp only [Polynomial.map_C, Rat.coe_castHom]
  rw [hc, H, Polynomial.derivative_map, ← hd, ← Polynomial.map_mul, ← Polynomial.map_sub,
    Polynomial.coeff_map, hm]
  simp only [Rat.coe_castHom, Rat.cast_div, abs_div, MiddleIntRow.spectralCutCoeff, Rat.cast_abs]

/-- One rational contribution to the full spectral bound, using a cached
translation and the common integer inverse-height weights. -/
@[expose]
public def MiddleIntRow.spectralCharge (r q : MiddleIntRow) (d κ E : ℚ) (j : ℕ) : ℚ :=
  (κ * r.spectralFullCoeff j + 4 * E * q.spectralCutCoeff d j) * (j.factorial : ℚ) *
    ((middleSpectralTicks j : ℚ) / (10 ^ 12 * 14 ^ j))

/-- A checked translated row gives a scalar certificate for the middle
principal spectrum at every positive cutoff under RH. -/
public theorem middle_spectral_row_le (r q : MiddleIntRow) (N : ℕ) (hRH : RiemannHypothesis)
    {a b : ℤ} {d κ E : ℚ} {X : ℝ} (hX : 0 < X) (hd : 0 < d) (hκ : 0 ≤ κ) (hb : b ≠ 0)
    (hz : 0 < (a : ℚ) / b) (hr : r.den ≠ 0) (hs : r.nums.size ≤ N + 1) (ht : q.nums.size ≤ N + 1)
    (hN : N < 52) (hq : (r.shift N a b).poly N = q.poly N) (h0 : r.num 0 = 0) (h1 : r.num 1 = 0)
    (hE : (κ : ℝ) * Real.exp (-((d : ℝ) + 1 / 2) * (((a : ℚ) / b : ℚ) : ℝ)) ≤ (E : ℝ)) :
    let B := (r.poly N).map (Rat.castHom ℝ)
    let z := (((a : ℚ) / b : ℚ) : ℝ)
    |(κ : ℝ) * Real.exp (-((d : ℝ) + 1 / 2) * z) * ∑' ρ, principalCancelledTerm B (d : ℝ) z X ρ| ≤
      ((∑ j ∈ Finset.range (N + 1), r.spectralCharge q d κ E j : ℚ) : ℝ) := by
  intro B z
  have hB : B.eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    dsimp only [B]
    rw [Polynomial.coeff_map, r.poly_coeff_all N hs, h0, Int.cast_zero, zero_div, map_zero]
  have hB' : B.derivative.eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative, zero_add]
    dsimp only [B]
    rw [Polynomial.coeff_map, r.poly_coeff_all N hs, h1, Int.cast_zero, zero_div, map_zero,
      zero_mul]
  have hdeg : B.natDegree ≤ N :=
    Polynomial.natDegree_map_le.trans
      (Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _))
  have h :=
    middle_spectral_le_ticks B hRH (Rat.cast_nonneg.mpr hκ) (Rat.cast_pos.mpr hd)
      (Rat.cast_pos.mpr hz) hX hB hB' hdeg hN (fun j ↦ (r.spectralFullCoeff j : ℝ))
      (fun j ↦ (q.spectralCutCoeff d j : ℝ)) (fun j _ ↦ (spectral_full_coeff_eq r N hs j).le)
      (fun j _ ↦ (spectral_cut_coeff_eq r q N hr hb hq ht d j).le)
  dsimp only at h
  refine h.trans ?_
  rw [Rat.cast_sum]
  apply Finset.sum_le_sum
  intro j _
  simp only [MiddleIntRow.spectralCharge, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_pow]
  refine
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl ?_) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (by positivity))
  have hn : 0 ≤ (q.spectralCutCoeff d j : ℝ) :=
    Rat.cast_nonneg.mpr (div_nonneg (abs_nonneg _) (abs_nonneg _))
  rw [mul_assoc (4 : ℝ)]
  simp only [Rat.cast_div] at hE
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num only)) hn

end PseudoPrime.PrimeTestBounds.MillerRabin
