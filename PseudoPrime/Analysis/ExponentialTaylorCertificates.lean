/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialFixedPointBounds
public import Mathlib.Data.Rat.Cast.Order

/-! # Rational Taylor lower certificates for exponentials -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Reciprocal of a positive exponential Taylor upper envelope.
For nonnegative t with t/(n+1) at most one half, it bounds exp(-t)
from below. The expression uses exact rational arithmetic. -/
def gammaExpTaylorLower (t : ℚ) (n : ℕ) : ℚ :=
  ((∑ i ∈ Finset.range n, t ^ i / (i.factorial : ℚ)) + t ^ n / (n.factorial : ℚ) * 2)⁻¹

/-- The rational reciprocal Taylor envelope is below exp(-t) under
the nonnegative-height and geometric-tail conditions. Cast the finite
upper bound for exp(t) and reverse order under reciprocation.
This supplies the lower exponential input of finite ramp certificates. -/
theorem gamma_exp_taylor_lower_valid {t : ℚ} {n : ℕ} (ht : 0 ≤ t)
    (hsize : t / (n + 1 : ℕ) ≤ 1 / 2) : (gammaExpTaylorLower t n : ℝ) ≤ Real.exp (-(t : ℝ)) := by
  have htR : (0 : ℝ) ≤ t := (Rat.cast_nonneg (K := ℝ)).mpr ht
  have hsizeR := (Rat.cast_le (K := ℝ)).mpr hsize
  norm_num only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hsizeR
  have hu := exp_le_taylor_add_two_next htR hsizeR
  have hu0 := (Real.exp_pos (t : ℝ)).trans_le hu
  simp only [gammaExpTaylorLower, Rat.cast_inv, Rat.cast_add, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat, Real.exp_neg]
  exact (inv_le_inv₀ hu0 (Real.exp_pos (t : ℝ))).mpr hu

end PseudoPrime.Analysis
