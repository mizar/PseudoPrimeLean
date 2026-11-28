/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailMoment
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleExp

/-! # Rational certificates for fixed middle Euler cutoffs -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The lower endpoint of the exponential enclosure, as a rational divisor. -/
public def middleTailExpDen (n : ℕ) : ℚ :=
  ((gaussianMidExpGrid n).lower : ℚ) / 100000000

/-- Use the lower exponential endpoint directly as a divisor. This preserves
precision for very small exponentials without an extra reciprocal rounding. -/
public theorem middle_tail_exp_le (n : ℕ) (hn : 0 < middleTailExpDen n) :
    Real.exp (-((n : ℝ) / 80)) ≤ (1 / middleTailExpDen n : ℚ) := by
  have h := (gaussian_mid_exp_grid n).1
  have hh : (middleTailExpDen n : ℝ) ≤ Real.exp ((n : ℝ) / 80) := by
    simpa only [middleTailExpDen, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat,
      Int.cast_ofNat] using h
  rw [Real.exp_neg, Rat.cast_div, Rat.cast_one, inv_eq_one_div]
  exact one_div_le_one_div_of_le (Rat.cast_pos.mpr hn) hh

/-- Scalar rational checks bound the normalized Abel cost at a fixed cutoff.
The rates are supplied as grid indices for the two decaying exponentials. -/
public theorem middle_mass_tail_budget (Q : Polynomial ℚ) (a o κ : ℚ) (d : ℕ) (f : ℕ → ℚ)
    (hQ : Q.natDegree ≤ d) (hf : ∀ i ≤ d, f i = Q.coeff i) (n m : ℕ)
    (hn : (n : ℚ) / 80 = (a - 1 / 2) * o) (hm : (m : ℚ) / 80 = a * o) (hnp : 0 < middleTailExpDen n)
    (hmp : 0 < middleTailExpDen m) (M E B : ℚ) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hmain :
      κ *
          middleTailRowMoment (d + 1) (a - 1 / 2)
            (fun i ↦ (middleMassShiftRow a o d f)[i]?.getD 0) ≤
        M)
    (herr :
      κ * middleTailRowError (d + 1) a o (fun i ↦ (middleMassShiftRow a o d f)[i]?.getD 0) ≤ E)
    (hB : 4 * (M / middleTailExpDen n + E / middleTailExpDen m / 24) ≤ B) :
    4 * (κ : ℝ) * middleMassTailCost Q a d (Real.exp (o : ℝ)) ≤ (B : ℝ) := by
  have hnr : (n : ℝ) / 80 = ((a : ℝ) - 1 / 2) * (o : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_mul, Rat.cast_sub, Rat.cast_ofNat,
      Rat.cast_one] using congrArg (fun q : ℚ ↦ (q : ℝ)) hn
  have hmr : (m : ℝ) / 80 = (a : ℝ) * (o : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_mul, Rat.cast_ofNat] using
      congrArg (fun q : ℚ ↦ (q : ℝ)) hm
  have en := middle_tail_exp_le n hnp
  have em := middle_tail_exp_le m hmp
  rw [hnr, ← neg_mul] at en
  rw [hmr, ← neg_mul] at em
  have h₁ :=
    (mul_le_mul_of_nonneg_left (Rat.cast_le.mpr hmain)
          (Real.exp_pos (-((a : ℝ) - 1 / 2) * (o : ℝ))).le).trans
      (mul_le_mul_of_nonneg_right en (Rat.cast_nonneg.mpr hM))
  have h₂ :=
    (mul_le_mul_of_nonneg_left (Rat.cast_le.mpr herr) (Real.exp_pos (-(a : ℝ) * (o : ℝ))).le).trans
      (mul_le_mul_of_nonneg_right em (Rat.cast_nonneg.mpr hE))
  have hb :
    (4 : ℝ) * ((M : ℝ) / (middleTailExpDen n : ℝ) + (E : ℝ) / (middleTailExpDen m : ℝ) / 24) ≤
      (B : ℝ) := by
    exact_mod_cast hB
  rw [middle_mass_tail_rat Q a o d f hQ hf]
  simp only [Rat.cast_mul, one_div, Rat.cast_inv] at h₁ h₂ ⊢
  simp only [div_eq_mul_inv] at hb ⊢
  nlinarith only [h₁, h₂, hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
