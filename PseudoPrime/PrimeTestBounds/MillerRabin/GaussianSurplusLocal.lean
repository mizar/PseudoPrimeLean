/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusRoots
public import PseudoPrime.PrimeTestBounds.MillerRabin.MRLocalCutoffNumerics

/-! # Local subgroup coverage by a clipped Gaussian cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A clipped Gaussian radius with floor at least 130 and residual at least 29 covers
the local subgroup cutoff. The quadratic budget retains its additive residual, which
absorbs the logarithmic modulus term without a large lower bound on the scale. -/
theorem jointSurplus_local_cutoff {n q : ℕ} (hn : 0 < n) (hq : 0 < q) (hsize : q ^ 2 ≤ 10 ^ 12 * n)
    (hL : (0 : ℝ) ≤ Real.log n) {rho R : ℝ} (hrho : 130 ≤ rho) (hR : 29 ≤ R) :
    max (3000 : ℝ) (Real.log q ^ 2) ≤
      (21 / 10 : ℝ) * (jointSurplusRadius rho R (Real.log n)) ^ 2 := by
  let L := Real.log n
  let r := jointSurplusRadius rho R L
  have hr : rho ≤ r := le_max_left _ _
  have hr130 : (130 : ℝ) ≤ r := hrho.trans hr
  have hbudget :=
    jointSurplus_budget (rho := rho) (R := R) (L := L) (by linarith only [hrho])
      (by linarith only [hR]) hL
  change
    (20115621 / 25000000 : ℝ) * L + R + (28794111 / 12500000 : ℝ) * Real.sqrt r ≤
      (10971611 / 5000000 : ℝ) * r at hbudget
  have hsqrt : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hrad : L / 2 + 14 ≤ (7 / 5 : ℝ) * r := by nlinarith only [hbudget, hsqrt, hL, hR]
  have hN : (q : ℝ) ^ 2 ≤ (10 : ℝ) ^ 12 * n := by exact_mod_cast hsize
  have hlog := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hq) 2) hN
  rw [Real.log_pow, Real.log_mul (pow_ne_zero _ (by norm_num only)) (Nat.cast_pos.mpr hn).ne',
    Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hqlog : Real.log q ≤ (7 / 5 : ℝ) * r := by
    nlinarith only [hlog, log_ten_lt_seven_thirds, hrad]
  have hsq :=
    (sq_le_sq₀ (Real.log_natCast_nonneg q) (by nlinarith only [hr130] : 0 ≤ (7 / 5 : ℝ) * r)).mpr
      hqlog
  apply max_le
  · nlinarith only [hr130]
  · nlinarith only [hsq, sq_nonneg r]

end PseudoPrime.PrimeTestBounds.MillerRabin
