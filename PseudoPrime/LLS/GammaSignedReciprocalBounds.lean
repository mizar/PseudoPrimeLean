/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaEulerReciprocalBounds

public import PseudoPrime.LLS.GammaRamifiedFiniteSupport

/-! # Signed reciprocal envelopes and smaller dual support -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: x at least one and an integer p>1 beyond 1+6 sqrt x.
Claim: the signed dual excess vanishes. Proof: bound the Euler cost by 3/(2(p-1))
and the ramp count by one. Role: halve the former finite-support range. -/
theorem gamma_ramified_signed_excess_eq_zero_of_six_sqrt {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 1 ≤ x)
    (hpbig : 1 + 6 * Real.sqrt x < p) :
    max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedDualParameter x) 0 = 0 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ht0 := Real.sqrt_pos.mpr hx0
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hpp : 6 * Real.sqrt x < p := by linarith only [hpbig]
  have hs := (sq_lt_sq₀ (mul_nonneg (by norm_num only) ht0.le) (zero_lt_one.trans hpR).le).mpr hpp
  have hcut : (99 / 40 : ℝ) * x < (p : ℝ) ^ 2 := by nlinarith only [hs, Real.sq_sqrt hx0.le, hx]
  have he := Analysis.gamma_prime_euler_cost_le_signed_reciprocal hpR
  have hr := gamma_ramp_count_le_one_of_square_above hp hx hcut
  have hd : (3 / 2 : ℝ) / ((p : ℝ) - 1) < 1 / (4 * Real.sqrt x) := by
    apply (div_lt_div_iff₀ (sub_pos.mpr hpR) (mul_pos (by norm_num only) ht0)).mpr
    nlinarith only [hpbig]
  have hb := add_lt_add_of_lt_of_le (he.trans_lt hd) (div_le_div_of_nonneg_right hr ht0.le)
  have heq : (1 : ℝ) / (4 * Real.sqrt x) + 1 / Real.sqrt x = 5 / (4 * Real.sqrt x) := by
    rw [← div_div (1 : ℝ) 4 (Real.sqrt x), ← add_div]
    norm_num only
    rw [div_div]
  have hh : Analysis.gammaRamifiedCombinedCost p x < gammaRamifiedDualParameter x := by
    simpa only [Analysis.gammaRamifiedCombinedCost, gammaRamifiedDualParameter, heq] using hb
  exact max_eq_right (sub_nonpos.mpr ((gamma_ramified_signed_cost_le_combined hp hx0).trans hh.le))

end PseudoPrime.LLS
